"""Check integrity and replay the supplied finite certificates with Python 3."""
import hashlib
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BASE = ROOT / "submission018"


def verify_manifest(folder):
    for line in (folder / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        expected, name = line.split("  ", 1)
        path = folder / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"Digest mismatch for {path.relative_to(ROOT)}")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization.")
    for folder in (ROOT, BASE, BASE / "evidence/012", BASE / "evidence/013"):
        verify_manifest(folder)
    for script, args in [(BASE / "check_witnesses.py", []),
                         (BASE / "evidence/012/verify_submission.py", []),
                         (BASE / "checks/check_transfers.py", []),
                         (BASE / "checks/exit025/check_landing.py", []),
                         (ROOT / "review/check_recorded.py", [str(BASE)]),
                         (ROOT / "review/recount_states.py", [])]:
        subprocess.run([sys.executable, "-B", str(script), *args], cwd=ROOT, check=True)
    print("PASS 019 recorded-layer and witness checks")
