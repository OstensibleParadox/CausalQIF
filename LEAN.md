# LEAN 文件巡检（截至 2026-06-21）

本文件记录当前 `/Users/ostensible_paradox/Documents` 下的 Lean 清理状态，不再维护旧路径的全量文件清单。

## 活动 Canonical

- Canonical Lean 入口：`CausalQIF/lean/CausalQIF.lean`
- Canonical 源码树：`CausalQIF/lean/CausalQIF/`
- 构建根包名：`causal_qif` / `CausalQIF`

## 清理结果

- 已清理不保留的旧项目树：
  - `popl27/`
  - `archive_memos/CasualQIF/`
  - `CausalQIF/archive/`（历史归档目录已移除）
- 活动树目前为主，不再保留上述路径下的 `.lean` 重复镜像文件树。
- 全库重复 `.lean` 哈希组数：`0`
- `lean_files_sorted.md` 中的历史“全量列表”已仅保留作归档记录，不再作为当前活动索引。

## 当前核验命令

- `python3 find_lean.py`
- `rg -n "FiniteQuerySandbox|CasualQIF|/Users/ostensible_paradox/Documents/(popl27|archive_memos/CasualQIF)" -g "*.lean" -g "*.md" -g "*.toml"`
- `rg -n \"FiniteQuerySandbox|CasualQIF|\\blegacy\\b\" CausalQIF/lean/CausalQIF CausalQIF/docs CausalQIF/provenance`
