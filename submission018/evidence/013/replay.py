"""Recompile the fixed-target Lean supplement and audit each reported theorem."""
import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"
NAMESPACE = "Candidate.AK3Peak.FixedS."
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = {
    "compulsory_through_43": "cap22_r17_r26",
    "exact22_deleted": "cap22_r17_r26",
    "exact22_to24": "cap24_r15_r26",
    "exact23_to24_deleted": "cap24_r15_r26",
    "reachable_in_41_iff": "cap24_r15_r26",
    "exact25_to26": "cap26_r16_r24",
    "forty_requires_27": "cap26_r16_r24",
    "cap30_at_least_24": "cap30_r8_r15",
}


def audit(log, name):
    content = log.read_text()
    results = {}
    declarations = re.findall(r"^#print axioms (\S+)", (SRC / (name+".lean")).read_text(), re.M)
    if not declarations:
        raise ValueError("No declarations to audit")
    for decl in declarations:
        escaped = re.escape(decl)
        match = re.search(r"'"+escaped+r"' depends on axioms:\s*\[([^\]]*)\]", content)
        if match:
            axioms = {x.strip() for x in match[1].split(",")}
        elif re.search(r"'"+escaped+r"' does not depend on any axioms", content):
            axioms = set()
        else:
            raise ValueError("Missing axiom report for "+decl)
        extension = NATIVE.get(decl.removeprefix(NAMESPACE))
        expected = {NAMESPACE+extension+"._native.decide.ax_1_1"} if extension else set()
        if axioms - STANDARD != expected:
            raise ValueError(f"Unexpected axioms for {decl}: {sorted(axioms)}")
        results[decl] = sorted(axioms)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["kernel","through24","through26","cap30-pilot","all"])
    parser.add_argument("output", type=Path, help="fresh directory for logs and compiled modules")
    parser.add_argument("--project", type=Path, default=ROOT/"pinned", help="built pinned baseline project")
    args = parser.parse_args()
    project = args.project.resolve()
    out = args.output.resolve()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    version = subprocess.check_output(["lean","--version"],text=True,cwd=project).strip()
    if "version 4.35.0," not in version or "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" not in version:
        sys.exit("The pinned Linux Lean 4.35.0 compiler is required")
    for rel, expected in json.loads((ROOT/"baseline_git_blobs.json").read_text()).items():
        data = (project/rel).read_bytes()
        header = ("blob " + str(len(data))).encode() + bytes([0])
        if hashlib.sha1(header + data).hexdigest() != expected:
            sys.exit("Baseline differs at "+rel)
    packages = json.loads((project/"lake-manifest.json").read_text())["packages"]
    for rec in packages:
        cwd = project/".lake/packages"/rec["name"]
        rev = subprocess.check_output(["git","rev-parse","HEAD"],text=True,cwd=cwd).strip()
        if rev != rec["rev"]:
            sys.exit("Dependency revision differs for "+rec["name"])
    pinned_path = subprocess.check_output(["lake","env","printenv","LEAN_PATH"],cwd=project,text=True).strip()
    env["LEAN_PATH"] = os.pathsep.join([str(out),pinned_path])
    out.mkdir(parents=True, exist_ok=False)
    results, axioms = [], {}

    def invoke(name, cmd):
        start=time.monotonic()
        log=out/(name+".log")
        with log.open("w") as sink:
            proc=subprocess.run(cmd,cwd=SRC,env=env,stdout=sink,stderr=subprocess.STDOUT)
        results.append(dict(name=name,exit=proc.returncode,elapsed_s=round(time.monotonic()-start,2)))
        (out/"stages.json").write_text(json.dumps(results,indent=2)+"\n")
        if proc.returncode or re.search(r"\b(?:sorryAx|sorry)\b|: (?:error|warning):", log.read_text()):
            raise SystemExit(f"Check failed at {name}. See {log}")
        if name.startswith("Audit"):
            axioms.update(audit(log,name))
        print(f"{name} OK",flush=True)

    def module(name, plugins=(), generate_c=False):
        opts=["lean","-j1","-M7600"]
        if name=="LayerPilot":
            opts.append("-DmaxRecDepth=20000")
        opts.extend("--plugin="+str(out/(p+".so")) for p in plugins)
        if generate_c:
            opts.extend(["-c",str(out/(name+".c"))])
        invoke(name,opts+["-o",str(out/(name+".olean")),name+".lean"])

    def library(name, dependencies=()):
        cmd=["leanc","-O3","-DLEAN_EXPORTING","-fPIC","-shared","-o",str(out/(name+".so")),str(out/(name+".c"))]
        if dependencies:
            cmd.extend(["-L"+str(out),"-Wl,-rpath,$ORIGIN"])
            cmd.extend("-l:"+lib+".so" for lib in dependencies)
        invoke(name+"-shared",cmd)

    base_engine = "B5BallEngine"
    engine = "CompactEngine"
    bank = "BankEngine"
    for name in ("FixedSWitness","FixedSPaths","ThroughEdge","FixedSCuts","FixedSCycles","PathCount","RecordedCounts",
                 "CountSemantics","PairedPaths","StreamCut",base_engine,"B5BallSearch",engine,"CompactSound",bank,"BankSound","LayerChecks","LayerPilot","AuditKernel"):
        module(name,generate_c=(args.mode!="kernel" and name in (base_engine,engine,bank)))
    if args.mode!="kernel":
        library(base_engine)
        if args.mode in ("through24","through26","all"):
            library(engine,[base_engine])
            for name in ("Cap22Compute","Cap24Compute"):
                module(name,[base_engine,engine])
            module("Confirmed24")
            module("EdgeNecessity")
            module("Audit24")
        if args.mode in ("through26","all"):
            library(bank,[engine,base_engine])
            plugins=[base_engine,engine,bank]
            module("BankPilot",plugins)
            module("Cap26Compute",plugins)
            module("Confirmed26")
            module("Audit26")
        if args.mode in ("cap30-pilot","all"):
            module("Cap30Lower",[base_engine])
            module("Audit30Pilot")
    targets=["FixedSWitness","FixedSPaths","ThroughEdge","FixedSCycles","FixedSCuts","CompactSound","BankSound",
             "PathCount","RecordedCounts","CountSemantics","PairedPaths","StreamCut","LayerChecks","LayerPilot"]
    if args.mode in ("through24","through26","all"):
        targets.extend(["Confirmed24","EdgeNecessity"])
    if args.mode in ("through26","all"):
        targets.append("Confirmed26")
    if args.mode in ("cap30-pilot","all"):
        targets.append("Cap30Lower")
    invoke("module-replay",["leanchecker","-v",*targets])
    receipt=dict(lean=version,mode=args.mode,theorems=axioms,
                 largest_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    (out/"axioms.json").write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(f"PASS {len(axioms)} declaration audits",flush=True)


if __name__ == "__main__":
    main()
