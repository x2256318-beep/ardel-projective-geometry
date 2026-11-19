あなたは Lean 4 / Mathlib の形式文を読む照合者です。ファイル /home/claude/ardel-projective-geometry/records/audit264/input_formal.md だけを Read で読んでください（ほかのファイルを読まない、コードを実行しない、ウェブを使わない）。答えは日本語で書いてください。「正しいか」の判定は要りません。次の成果物を出してください。

1. 逆翻訳：A の各 theorem の文を、Lean の記号を使わずに普通の数学の文に直す（仮定をすべて含めて）。主な定義（fsum、cornerOp、cornerHom）も言葉で書く。
2. 非空虚性の証人：主な定理（cornerOp_mem、existsUnique_corner、cornerOp_comp、cornerHom_comp、cornerOp_one、cornerOp_geps、cornerOp_dind、cornerOp_one_ne_one、cornerOp_dind_not_mem_span）について、仮定をすべて満たす具体例（N, M などの値）を挙げ、そのとき文が何を言っているかを具体的に書く。仮定が満たせない・文が自明になる場合はそう書く。
3. 除去テスト：主な定理の仮定を 1 つずつ外した文を考え、小さいパラメータで反例が作れるか（作れるなら具体的に）、外しても成り立つなら「その仮定は不要に見える」と書く。とくに existsUnique_corner の 2 つの条件それぞれを外した場合。
4. 気づいた点：文が意図と違って読める可能性（例：添字の取り違え、0 や 1 での退化、`M / N` の自然数の割り算、型の扱い）があれば挙げる。

最後に、使ったツールの回数と、読んだ範囲を書いてください。