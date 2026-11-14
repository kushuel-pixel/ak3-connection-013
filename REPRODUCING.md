# Gitスナップショットの再現手順

LinuxでこのREADMEと同じディレクトリから実行する。Python 3、全B15走査にはC++17対応の g++ を使う。公開ファイルのSHA-256と付録の独立したマニフェストを検査するには次の2行を実行する。

```sh
sha256sum --quiet -c SHA256SUMS
python3 -B appendix003_C1/checkers/check_manifest.py
```

## 有限計算

検算器は計算結果を付録内に書くので、作業用コピーで実行する。

```sh
work_dir=$(mktemp -d)
cp -R appendix003_C1 "$work_dir/appendix"
python3 -B "$work_dir/appendix/checkers/check_appendix.py"
python3 -B "$work_dir/appendix/checkers/replay_B15.py"
```

最初の検算は6-mixの残余16配置（符号付き156＋16プロファイル）と双対証明書の全3,364列を含む。次の走査では半径15の共役語球を左右別々に列挙する。正側3分割の共通類は0。負側の共通類の長さは6・16・26・28・36で、このうち32以下は4類。各子プロセスの上限は仮想アドレス空間4 GiB、CPU 90/91秒（soft/hard）、wall 150秒。[元の再実行記録](review007/reviewers/compute/scanner_runs/FULL_REPLAY_RESULT.json)

負側の標準出力には実測値 `wall_seconds` があるため、同じ共通類が得られても `stdout_sha256` は実行ごとに変わり得る。照合する値は列挙数、distinct数、共通類の語と長さ。[元の負側出力](appendix003_C1/verification/B15_replay/negative.stdout.json)

## Lean

前提はLinux、Git、curl、Python 3、[Elan](https://github.com/leanprover/elan)（`elan`・`lean`・`lake` がPATH上にあること）。初回は公開のLean配布元、GitHubおよびmathlibのビルドキャッシュへのネットワーク接続を使う。以下のブロックはこのリポジトリのルート から順に、同じシェルで実行する。

Claudeが固定コミット `4f0c588` を空の環境で追試した際、初回の依存取得からREADMEの最小例の型検査まで、以下の3ブロックでディスクを約4.3 GB使用し、所要時間は約4分だった。時間はマシンと回線によって変わる。[追試の内訳](VERIFICATION.md#claudes-lean-recheck-at-4f0c588)

### 1. 空のディレクトリに固定依存を準備する

付属の [Lake設定](verification/deps-project/lakefile.toml)、[ロックファイル](sources/submission001/lean/lake-manifest.json)、[ツールチェーン指定](sources/submission001/lean/lean-toolchain) を使う。Lakeはロックされた公開9依存を取得する。キャッシュ取得の引数は、証明が直接インポートする6個のMathlibモジュールで、推移的な依存も取得される。

```sh
set -eu
snapshot=$(pwd -P)
work_dir=$(mktemp -d)
deps_project="$work_dir/deps"
mkdir "$deps_project"
cp verification/deps-project/lakefile.toml "$deps_project/"
cp sources/submission001/lean/lean-toolchain sources/submission001/lean/lake-manifest.json "$deps_project/"
(
  cd "$deps_project"
  elan toolchain install "$(cat lean-toolchain)"
  MATHLIB_CACHE_DIR="$work_dir/mathlib-cache" lake exe cache get \
    Mathlib.Algebra.Group.Conj Mathlib.Algebra.Group.End \
    Mathlib.GroupTheory.FreeGroup.CyclicallyReduced Mathlib.Tactic.Group \
    Mathlib.Tactic.IntervalCases Mathlib.Tactic.Ring
)
cmp "$snapshot/sources/submission001/lean/lake-manifest.json" "$deps_project/lake-manifest.json"
runtime=$(cd "$deps_project" && lean --print-prefix)
```

既に対応する環境を用意してある場合は、このブロックの代わりに `runtime` にLean 4.35.0のインストール先、`deps_project` に固定9依存をビルド済みのプロジェクトの絶対パス、`work_dir` に新しい一時ディレクトリを設定して次へ進む。

### 2. ローカル証明と公理集合を検査する

`leanchecker` が子プロセスとして起動する `lean` にも同じ版を使うよう、このコマンドのPATHの先頭に固定版のbinディレクトリを指定する。

```sh
PATH="$runtime/bin:$PATH" python3 -B verification/run_lean.py \
  --runtime "$runtime" --deps-project "$deps_project" \
  --output "$work_dir/lean" --kernel
```

入口はロックファイルのバイト一致・全9依存のGit HEADと追跡ファイルの状態を確認し、31モジュールを新しく構築する。34宣言の型・公理集合、継承4契約、正例20件・拒否例6件を照合し、選択3モジュールを同一カーネルで再検査する。終了値0が成功。結果は `$work_dir/lean/RESULT.json` に残る。[検証入口のソース](verification/run_lean.py)

### 3. READMEの例を同じビルドで型検査する

```sh
python3 -B - "$work_dir/lean" <<'PYTHON'
import json
import os
from pathlib import Path
import re
import subprocess
import sys

build = Path(sys.argv[1]).resolve()
settings = json.loads((build / "BUILD_ENV.json").read_text())
blocks = re.findall(r"^```lean\n(.*?)^```$", Path("README.md").read_text(), re.M | re.S)
if len(blocks) != 1:
    raise SystemExit("Expected one Lean example in README.md")
example = build / "ReadmeExample.lean"
example.write_text(blocks[0])
env = dict(os.environ, LEAN_PATH=settings["LEAN_PATH"], LEAN_NUM_THREADS="1")
subprocess.run([settings["LEAN_BIN"], "-j1", "-M4096", example.name],
               cwd=build, env=env, check=True)
PYTHON
```

終了値0なら、このREADMEに掲載されている例が今回のビルドで型検査を通ったことになる。
