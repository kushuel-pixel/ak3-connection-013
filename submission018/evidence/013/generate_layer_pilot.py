"""Read the first physical cap-30 shards and render the proposed Lean layer keys."""
import argparse
import hashlib
import json
import struct
from pathlib import Path


def reduced_block(z):
    return all(((z >> (2*j) ^ z >> (2*j+2)) & 3) != 1 for j in range(8))


def unpack(key, blocks):
    m = key & 31
    if key >> 62 == 1:
        k = 42 if m <= 21 else 2*(m-9)
        compact = (key ^ (1 << 62)) >> 5
        rank = (compact >> k) & 32767
        joined = (1 << 60) | (compact >> (k+15) << (k+18)) | (blocks[rank] << k) | (compact & ((1 << k)-1))
    else:
        joined = key >> 5
    total = (joined.bit_length()-1)//2
    if m > total or joined >> (2*total) != 1:
        raise ValueError("Invalid word split or leading digit")
    digits = [(joined >> (2*i)) & 3 for i in reversed(range(total))]
    return digits[:total-m], digits[total-m:]


def lean_key(state):
    u,v = state
    n = 1
    for a in reversed(v):
        n = 4*n + a
    n = 5*n + 4
    for a in reversed(u):
        n = 5*n + a
    return n


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("stage",type=Path,help="stage 009 from review kit 012")
    p.add_argument("a_tables",type=Path)
    p.add_argument("s_tables",type=Path)
    p.add_argument("output",type=Path)
    args=p.parse_args()
    blocks=[z for z in range(1<<18) if reduced_block(z)]
    assert len(blocks)==26244
    src=["import LayerChecks","","namespace Candidate.AK3Peak.FixedS.LayerPilot","open Verify.AtomicSemantics",
         "open LayerChecks (members checks cover_of_checks)",""]
    for side,root,last,vertex in [("A",args.a_tables,2,"ak3"),("S",args.s_tables,3,"source")]:
        record=json.loads((args.stage/f"shards{side}30.json").read_text())
        src.extend([f"def rows{side} : LayerChecks.RowsByDepth"])
        for d in range(last+1):
            raw=[]
            layer=record["layers"][d]
            assert layer["depth"]==d and len(layer["shards"])==64
            for shard,(n,expected) in enumerate(layer["shards"]):
                blob=(root/f"{d}_{shard}.bin").read_bytes()
                if len(blob)!=8*n or hashlib.sha256(blob).hexdigest()!=expected:
                    raise ValueError(f"{side} depth {d} shard {shard} differs from the frozen record")
                raw.extend(w[0] for w in struct.iter_unpack("<Q",blob))
            keys=sorted(lean_key(unpack(k,blocks)) for k in raw)
            assert len(keys)==len(set(keys))==layer["total"]
            src.append(f"  | {d} => ["+", ".join(map(str,keys))+"]")
        src.extend(["  | _ => []","",
            f"theorem cover{side} : StreamCut.Cover 30 {last} {vertex} (members rows{side}) :=",
            "  cover_of_checks (by decide +kernel) (by decide +kernel)",""])
    src.extend(["end Candidate.AK3Peak.FixedS.LayerPilot",""])
    args.output.write_text("\n".join(src))


if __name__ == "__main__":
    main()
