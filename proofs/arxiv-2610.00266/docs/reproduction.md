# Public pinned reproduction

From the repository root:

```sh
python3 scripts/verify_arxiv_2610.py --dest /absolute/new/reproduction/path
```

The destination must not exist and must be outside the source repository. The default revision is the current immutable HEAD; use `--revision COMMIT` to select another available commit.

The wrapper reconstructs all nine public dependency commits from the nested Lake manifest, independently installs the hash-checked compiler, restores the pinned ProofWidgets display assets, and starts with no project build outputs. It runs the full strict gate without skip flags and preserves command logs and input hashes. The copied Git snapshot is separate from any research checkout.

Default `--dependency-mode official-cache` obtains public Mathlib dependency caches in the reproduction's own cache directory. This is a clean project rebuild using public dependency caches, not recompilation of every dependency.

Use `--dependency-mode source` to compile the required dependency modules from the pinned public source instead. Lake's automatic binary cache is disabled. Neither mode rebuilds Lean from C++ source.

An optional `--compiler-archive /absolute/path/to/archive.tar.zst` supplies the original official distribution archive. The wrapper checks the pinned SHA-256 and extracts it afresh. An installed toolchain directory is not accepted as a substitute.

Linux x86_64 and macOS ARM64 compiler assets are pinned. Required host tools are Git, Python 3.10+, curl, tar and zstd. Allow several hours and substantial free disk space for the complete independent-type/original-body audit. Use the wrapper's actual help output for current options.

The frozen nested `scripts/reproduce.py` retains an earlier root-layout/local-dependency interface to preserve the source-bound checker inventory. It is not the supported public entry point for this nested release. No server alias, private dependency checkout or author-local absolute path is needed by the public wrapper.
