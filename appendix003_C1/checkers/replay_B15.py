#!/usr/bin/env python3
"""Recompile and replay the two preserved review scanners (Linux, g++).

Each child has 4 GiB address-space, 90/91 second CPU, 150 second wall limits.
Runs sequentially. This is a fresh author-side replay of historical review
implementations, not a new independent review of the English appendix.
"""
from pathlib import Path
import hashlib, json, resource, subprocess, tempfile, time

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/B15_replay'
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(2**32,2**32))
    resource.setrlimit(resource.RLIMIT_CPU,(90,91))
def main():
    OUT.mkdir(parents=True,exist_ok=True)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='appendix003_') as tmp:
        for kind,name in [('positive','positive_B15_review055.cpp'),('negative','negative_B15_review028.cpp')]:
            source=ROOT/'checkers'/name; exe=Path(tmp)/kind
            subprocess.run(['g++','-O3','-std=c++17',str(source),'-o',str(exe)],check=True,timeout=60)
            for partition in (range(3) if kind=='positive' else [None]):
                args=['--scan','15',str(partition)] if kind=='positive' else ['15']
                label=kind+(str(partition) if partition is not None else '')
                started=time.monotonic()
                p=subprocess.run([str(exe)]+args,capture_output=True,timeout=150,preexec_fn=limits)
                (OUT/(label+'.stdout.json')).write_bytes(p.stdout)
                (OUT/(label+'.stderr.txt')).write_bytes(p.stderr)
                assert p.returncode==0,(label,p.returncode,p.stderr.decode())
                d=json.loads(p.stdout);assert d['tested_forward']==d['tested_backward']==28697813
                if kind=='positive':
                    old=json.loads((ROOT/'provenance/positive_B15_review055.json').read_text())['full_partitions'][partition]
                    assert d==old
                else:
                    classes=json.loads((ROOT/'data/common_classes.json').read_text())
                    expected={x['word'] for x in classes['classes']}|{x['word'] for x in classes['outside_length32']}
                    assert {x['word'] for x in d['shared_words']}==expected
                    assert d['distinct_forward']==28501106
                row={'case':label,'exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-started,3),
                     'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                     'stdout_sha256':hashlib.sha256(p.stdout).hexdigest(),
                     'stderr_sha256':hashlib.sha256(p.stderr).hexdigest(),
                     'unique_conjugators_each_side':28697813,'distinct_forward':d['distinct_forward'],
                     'common_classes':len(d['common_words'] if kind=='positive' else d['shared_words'])}
                rows.append(row);print(json.dumps(row),flush=True)
    result={'status':'PASS_FRESH_AUTHOR_REPLAY_OF_REVIEW028_055_SCANNERS','runs':rows,
      'positive_distinct_forward_sum':sum(x['distinct_forward'] for x in rows if x['case'].startswith('positive')),
      'positive_common_classes':0,'negative_common_classes':5,'negative_common_classes_length_at_most32':4,
      'address_space_bytes_per_child':2**32,'CPU_soft_hard_seconds':[90,91],
      'wall_timeout_seconds_per_child':150,'full_negative_and_three_positive_partitions_completed':True,
      'new_independent_review_of_appendix003':False}
    assert result['positive_distinct_forward_sum']==28501105
    (OUT/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],flush=True)
if __name__=='__main__':main()
