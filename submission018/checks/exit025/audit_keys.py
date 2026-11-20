"""Scan the pinned little-endian 128-bit key file and compute endpoint keys independently."""
import hashlib
import itertools
import json
import struct
import sys
from collections import Counter
from pathlib import Path

EXPECTED = "e62f7a0a24f993b22ec06edd625ffbbc3a9e2fa30d215b911834e1741c4aa0e4"
COUNT = 8_694_374
PAIRS = {
    "A": ("xyxYXY", "xxxYYYY"),
    "S": ("XyyyxYYYY", "xxYYYYYXyyyyy"),
    "E3": ("XyyyxYYYY", "xxYYYYXyyyy"),
    "T": ("x", "y"),
    "landing": ("yyyyxYXyxYYYxyyyy", "YYYYXXYYYYX"),
}


def cyclic_core(word):
    reduced = []
    for c in word:
        if reduced and reduced[-1] == (c ^ 1):
            reduced.pop()
        else:
            reduced.append(c)
    lo, hi = 0, len(reduced)
    while hi - lo >= 2 and reduced[lo] == (reduced[hi - 1] ^ 1):
        lo, hi = lo + 1, hi - 1
    return tuple(reduced[lo:hi])


def canonical_word(w):
    inverse = tuple(c ^ 1 for c in reversed(w))
    return min(z[k:] + z[:k] for z in (w, inverse) for k in range(len(z)))


def key(pair):
    a, b = [cyclic_core("xXyY".index(c) for c in w) for w in pair]
    keys = []
    for x, y in itertools.product(range(4), repeat=2):
        if x // 2 == y // 2:
            continue
        rename = (x, x ^ 1, y, y ^ 1)
        u, v = sorted((canonical_word(tuple(rename[c] for c in w)) for w in (a, b)),
                      key=lambda w: (len(w), w))
        payload = 0
        for c in u + v:
            payload = 4 * payload + c
        keys.append((len(u) << 122) | (len(v) << 116) | payload)
    return min(keys)


def main(path):
    target = {key(pair): name for name, pair in PAIRS.items()}
    if len(target) != len(PAIRS):
        raise ValueError("Expected distinct projected endpoint keys")
    found = {name: False for name in PAIRS}
    histogram = Counter()
    min_cost = 10**3
    min_rows = set()
    sha = hashlib.sha256()
    with path.open("rb") as reader:
        while block := reader.read(16 * 65536):
            sha.update(block)
            for low, high in struct.iter_unpack("<QQ", block):
                a, b = high >> 58, (high >> 52) & 63
                if not (1 <= a <= b and a + b <= 28):
                    raise ValueError("Invalid key lengths")
                histogram[a + b] += 1
                # Either row may be kept. Keeping the shorter one gives the largest budget.
                cost = 2 * a + b
                if cost < min_cost:
                    min_cost = cost
                    min_rows.clear()
                if cost == min_cost:
                    min_rows.add((a, b))
                name = target.get((high << 64) | low)
                if name:
                    found[name] = True
    max_bridge = (28 - min_cost) // 2
    result = {"min_weighted_length": min_cost, "minimizing_row_lengths": sorted(min_rows),
              "sha256": sha.hexdigest(), "keys": sum(histogram.values()),
              "length_histogram": dict(sorted(histogram.items())),
              "max_junction_free_budget_over_both_row_choices": max_bridge,
              "membership": found}
    print(json.dumps(result, indent=2))
    if (sha.hexdigest() != EXPECTED or sum(histogram.values()) != COUNT
            or min(histogram) != 13 or max_bridge != 4
            or found != {"A": True, "S": True, "E3": False, "T": False, "landing": False}):
        raise SystemExit("Key audit failed")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
