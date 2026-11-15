# 引き継ぎメモ（final76 → final77）：内部照合の監査（2026-11-14）を書き足す。
SRC = '/home/claude/out/final76/PAG2_handoff_part256_reaudit.md'
DST = '/home/claude/out/final77/PAG2_handoff_internal_audit.md'
s = open(SRC, encoding='utf-8').read()
def rep(a, b):
    global s
    assert s.count(a) == 1, a[:50]
    s = s.replace(a, b)
rep('# PAG 2.0 引き継ぎメモ（著者側の補足3 の開始条件を処理した時点、2026-11-14。Part 257 は始めていない）',
    '# PAG 2.0 引き継ぎメモ（内部照合の監査の時点、2026-11-14。Part 257 は始めていない）')
rep('## 進め方のルール（そのまま継続）\n',
    '## 進め方のルール（そのまま継続）\n'
    '- **（2026-11-14 著者の判断）内部照合を必須にする**：着手前の 4 点とパートを閉じる条件に、自分の鎖（xlsx の「定理と証明」と Lean の全宣言）の検索と、Lean での一致の確認を足す。CLAUDE.md への条文化は著者側（条文の案は `pag2_internal_audit_249_256.md` の付録）。道具は `audit_internal/`（`lean/Extract2.lean`：全宣言の定数、`shortlist2.py`：候補選び、`lean/DupCmd2.lean`：`#dupcheck`・`#defeqcheck`）。鎖に import されていない初めのファイル（PAG3・PAG5・PAG6）も対象に含める。照合者には Grep の代わりに読める形（ファイルごとの文）を渡すか、読み取り専用の grep を許す（今回は Grep が使えず、照合者は全宣言の文の 1〜3 割しか読めなかった）。\n'
    '- **（2026-11-14 内部照合の教訓）新しい定義を作る前に、同じ式の定義が鎖にないか探す。** `prodChar` は Part 195 の `cmul`・Part 232 の `charMul` と同じ定義（3 つ目の名前）、`crtMap` は Part 189 の `param`、`charU` は Part 1 の `PAG.charFun`、Part 253 の `ip` は Part 249 の `ipG` と同じだった。既にある定理（例：Part 189 の `gaussSum_mul_coprime`）は使い、示し直さない。\n')
rep('  2. 方向βの事前登録の扱いの明記（段階 1 でどうなったか。著者側の登録 `preregistration-part255-beta-premise.md` は開いたまま）。→ **未了**。登録の本文がこちらに届いていない（`pag2_beta_registration_status.md`）。本文が届いたら、Part 255 の結果と 1 項目ずつ突き合わせて閉じる。',
    '  2. 方向βの事前登録の扱いの明記（段階 1 でどうなったか。著者側の登録 `preregistration-part255-beta-premise.md` は開いたまま）。→ **未了**。登録の本文がこちらに届いていない（`pag2_beta_registration_status.md`）。本文が届いたら、Part 255 の結果と 1 項目ずつ突き合わせて閉じる。**2026-11-14 の著者の判断：監査は進め、Part 257 は登録ファイルが届くまで待つ。**')
rep('- 次の番号：Part 257 ＝ PAG261 ＝ step280。xlsx は 3552 項目・手順 277 から続ける（手順 277 は 2026-11-14 の再照合。',
    '- 次の番号：Part 257 ＝ PAG261 ＝ step280。xlsx は 3552 項目・手順 278 から続ける（手順 278 は 2026-11-14 の内部照合の監査、手順 277 は同日の再照合。')
AUDIT = '''## 内部照合の監査（2026-11-14、`pag2_internal_audit_249_256.md`）

- きっかけ：Part 257 の着手前の文書（`pag2_part257_preregistration.md`）を書く途中で、Part 256 の `gaussSum_prodChar`・`isPrimitive_prodChar` が Part 189・190 の定理と同じ文だと分かった。著者が監査を選んだ（新しいパートは始めない）。
- 方法：Part 249〜256 の宣言 334 件について、前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）の宣言 4279 件から候補を機械的に選び、一方を他方にそのまま当てる確認を約 1 万 3 千組。独立の照合者 5 人（形式文の全文、Read だけ）。照合者の A・B の判定を Lean で確かめ（`audit_internal/lean/ManualChecks.lean`）、C の判定から 4 件を標本として Lean で確かめた（`SampleC.lean`、すべて当たり）。
- 結果（前の鎖に対して）：
  - Part 252：A・B が 7（χ(−1) の補題 3 つは Part 5・21・25・77・167 と同じ文、`casKer` は付録 A の Part 3 の `casK`、`rootNum` は Part 192 の `zN` ÷ Part 194 の `gs`）。C が 12。**Hartley の部分は付録 A の Part 3（PAG3.lean、命題 2.8 `hartley_char`）とほぼ重なる。**
  - Part 253：A・B が 6（`charU` は Part 1 の `PAG.charFun`、ほかは Part 26・28・191・194 から直ちに出る）。C が 2。範囲の中で `ip` は Part 249 の `ipG`。
  - Part 254：B が 1（`gaussSum_inv`）、C が 2。
  - Part 256：A・B が 12（前半はほぼ全部が Part 189・190・195・232 の示し直し。`crossSign` は Part 194 の `rs`）。C が 3。相互法則は Part 194 の `real_reciprocity` に仮定なしである。
  - Part 251：C が 1。Part 249・250・255：前の鎖との重複は見つからなかった。
- 直したもの：PAG255〜PAG258・PAG260 の docstring と冒頭（形式文は変えていない。PAG255〜PAG260 を組み立て直し、.out は同一）、Part 249〜256 のノート（「内部照合」の節）、Part 256 の着手前の文書の訂正、xlsx（Part 251〜256 の行の「証明の方針」43 か所、Part 252・253・256 の見出し、手順 278、メモ）。
- 限界：照合者は Grep が使えず、全宣言の文の 1〜3 割しか読めていない。機械的な候補選びは上位 20 件まで。「見つからなかった」は「ない」の証明ではない。
- 前の鎖の中どうしの重複（範囲外、記録だけ）：`cmul`（Part 195）と `charMul`（Part 232）、χ(−1) の補題（Part 5・21・25・77）、`lam_pos`（Part 27・42・112）、`ip`（Part 48）と `herm`（Part 225）など。監査の報告の §6。

'''
rep('## 収束アラームの状況（CLAUDE.md §7、再照合の後、2026-11-14）',
    AUDIT + '## 収束アラームの状況（CLAUDE.md §7、内部照合の後、2026-11-14）\n\n'
    '- 兆候 4（初等的な部品だけ）：Part 249〜256 の 8 パート連続のまま（新しいパートは始めていない）。内部照合で、Part 252・256 の一部は「既知の事実の Lean 化」ではなく「鎖の中にある定理の示し直し」だったと分かった。\n'
    '- 兆候 1 の内側版：自前の名前が、自分の鎖の既存の定義と同じだった（`prodChar`・`crtMap`・`charU`・`ip`）。\n'
    '- 次のパートの前に：内部照合（上の規則）を着手前の 4 点に入れる。Part 257 の候補 P1・P2・P4 の中身の大半は鎖にある（`pag2_part257_preregistration.md` の §7）。\n\n'
    '## 収束アラームの状況（CLAUDE.md §7、再照合の後、2026-11-14。記録として残す）')
open(DST, 'w', encoding='utf-8').write(s)
print('saved', DST, len(s.split(chr(10))), 'lines')
