あなたは Lean 4 / Mathlib の形式文を読む照合者です。使ってよいのは Read だけで、読むのは次の 2 つのファイルだけです（コードの実行・ウェブ・ほかのファイルは使わない）。答えは日本語で書いてください。「正しいか」の判定は要りません。

手順：まず /home/claude/ardel-projective-geometry/records/audit265/input_formal.md だけを読み、成果物 1〜3 を書き終えてください。そのあとで /home/claude/ardel-projective-geometry/records/audit265/input_prose.md を読み、成果物 4 を書いてください。

1. 逆翻訳：A の各 theorem・def・instance・abbrev を、Lean の記号を使わない普通の数学の文に直す（仮定をすべて含めて）。
2. 非空虚性の証人：cornerSys_self・cornerSys_comp・cornerLim_of_injective について、仮定を満たす具体例（a, b, c の値）と、そのとき文が何を言っているか。文が自明になる場合はそう書く。
3. 除去テスト：仮定を 1 つずつ外した文や、添字の順序を整除から別の順序に替えた文で、反例が作れるか。とくに cornerLim_of_injective が何に依存しているか（遷移写像の単射性を外すとどうなるか）。
4. 散文（入力 2）が形式文（入力 1）より広い・強い・違う箇所、宣言名の取り違え、「Lean にしていない」と書いたものが本当に A にないか（逆に A にあるのに外と書いていないか）。該当箇所の引用と直し方つきで。問題がなければ「なし」。

最後に、使ったツールの回数と読んだ範囲を書いてください。