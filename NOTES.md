# lean_buzzard — Strand A: Formalising Mathematics (Buzzard 2024)

Strand A of the Lean track (Phase 1.2+, master Weeks 5–22). Topic-driven Buzzard
exercise sheets, picked by interest; goal is **breadth + Mathlib fluency, not speed**.
MIL work lives separately in `lean_learning` — don't duplicate it here.

Repo: fork of `ImperialCollegeLondon/formalising-mathematics-2024`
(`origin` = personal fork, `upstream` = official). Own pinned `lean-toolchain` +
Mathlib (early-2024), independent of MIL's 4.29.1.

Daily block format (dash bullets, inline backticks on tactic/lemma names):

    ## DD-MM-YYYY (Day, Week X.Y)
    - what was done
    - new tools added: `tactic1`, `LemmaFamily.foo`

---

# Progress log

## 07-06-2026 (Sunday, Week 5.0)
- Strand A setup: forked + cloned Buzzard `formalising-mathematics-2024` as `lean_buzzard` at `~/lean/lean_buzzard`, sibling to `lean_learning`; `origin` = fork, `upstream` = official, `lake exe cache get` done.
- Repo pins its own `lean-toolchain` + Mathlib (early-2024), independent of MIL's 4.29.1 — left as-is.
- Read Section 5 (groups), no proofs: Sheet 1 = tour of Mathlib group API (heavy `rw` on group axioms); Sheet 2 = build `WeakGroup`/`BadGroup` classes (the tricky one); Sheet 3 = subgroups + homomorphisms (`refine`/`ext`/`apply` practice).
- To check: which inverse-axiom name the pinned Mathlib uses (`mul_left_inv` vs `inv_mul_cancel`); `refine ?_` is the new tactic to learn.

## 08-06-2026 (Monday, Week 5.1)
- Section 5 Sheet 1 (groups) complete — worked all examples cold, axiom-threading by hand with `rw`/`calc`.
- Pinned-Mathlib group axioms confirmed: `inv_mul_self`, `mul_inv_self`, `mul_assoc`, `one_mul`, `mul_one` (resolves the inverse-axiom parking-lot item — `_self` naming, not `inv_mul_cancel`).
- Conceptual wall hit + cleared: anonymous `example` binds no name → promote to named `theorem`/`lemma` to reuse; pass explicit type-vars by name (`(a := 1)`) so Lean infers `G` from the goal.
- Found `inv_eq_iff_mul_eq_one` solo; meta-lesson — Mathlib often orients the iff opposite to a hand-built version, so check direction before `.mp`/`.mpr`.
- new tools added: `calc`, named `theorem`/`lemma` reuse pattern, `inv_eq_iff_mul_eq_one`, `inv_one`, `group`

## 09-06-2026 (Tuesday, Week 5.2)
- Section 5 Sheet 2 (WeakGroup/BadGroup) complete.
- WeakGroup: proved left axioms ⟹ right axioms via bootstrap chain `mul_left_cancel` → `mul_eq_of_eq_inv_mul` → `mul_one` → `mul_inv_self`. Each theorem may only use the ones above it — proof order = dependency order, can't forward-reference.
- Key move: `apply mul_left_cancel` to introduce a common left factor (`a⁻¹`), turning `a * b = c` into a cancellable goal; only left-handed axioms available so every step must be left-handed.
- BadGroup: all-`true` `Mul` fails `mul_one`; fixed with left-projection `a * b = a` (right identity holds, left identity breaks). All axiom obligations + the `¬∀ a, 1 * a = a` falsity close by `decide` on finite `Bool`.
- new tools added: `class ... extends One G, Mul G, Inv G ... where` (defining own typeclass), anonymous-constructor instances `⟨true⟩`, `decide` (now reliable on finite types), apply-to-set-up-cancellation pattern

## 10-06-2026 (Wednesday, Week 5.3)
- Section 5 Sheet 3 (subgroups + homomorphisms) complete — Section 5 (groups) fully done.
- Subgroups are terms, not types (like `Set`): closure facts via dot notation `H.mul_mem`, `H.one_mem`, `H.inv_mem`.
- Used `refine H.mul_mem ?_ ?_` to build a nested membership proof as a tree of named holes (clears the `refine ?_` parking-lot item).
- Lattice notation: `H ⊓ K` (intersection), `H ⊔ K` (generated), `H ≤ K`, `⊥`, `⊤`. `a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K` is `rfl`; for `⊔` only the `←` direction holds.
- `Subgroup.mem_sup_left` / `Subgroup.mem_sup_right` (both subgroup args implicit) for the `⊔` case.
- Meta-lesson: dot notation fills the FIRST argument whose type matches the receiver; if a lemma's hypothesis concerns a later same-typed argument (`mem_sup_right` is about the 2nd subgroup), dot misbinds — use the full `Namespace.lemma` name and let implicits infer (`exact Subgroup.mem_sup_right hk`).
- Homomorphisms: `G →* H`; preservation lemmas `φ.map_mul`, `φ.map_inv`, `φ.map_one`; `ext` reduces `φ = ψ` to pointwise `∀ g, φ g = ψ g`.
- new tools added: `refine` (named holes `?_`), `Subgroup.mul_mem`/`one_mem`/`inv_mem`, `Subgroup.mem_sup_left`/`mem_sup_right`, `MonoidHom.map_mul`/`map_inv`/`map_one`, `ext` for hom equality

## 11-06-2026 (Thursday, Week 5.4)
- Section navigation corrected from the actual repo tree: no quotients section; Section06 = orderings/lattices, Section13 = measure theory, Section17 = analysis (calculus/Lᵖ), NOT algebraic curves. High-fit sections: 15 numberTheory, 14 UFDs/PIDs, 16 commutativeAlgebra, 19 algebraicNumberTheory, 21 galoisTheory.
- Started Section 15 (Number Theory). Sheet 1 (Basic Number Theory) complete — mostly a casting tutorial.
- Casting toolkit: `norm_cast` (pull `↑` out + cancel), `push_cast` (push `↑` in to leaves, then `ring`), `exact_mod_cast`/`assumption_mod_cast` (one-shot up to coercions), `zify` (ℕ goal → ℤ, regain subtraction), `lift` (ℤ → ℕ with nonneg proof). Pairs: out/in and up/down.
- Solved `n+1 ∣ n²+1 ↔ n=1` via `zify` + divides-the-difference (`n+1 ∣ n²-1` and `∣ (n²+1)`, so `∣ 2`).
- Idioms from review: `⟨n-1, by ring⟩` (give divisibility witness directly via anonymous constructor) beats rewrite + `dvd_mul_right`; `Int.le_of_dvd (by norm_num) h` turns `d ∣ k` into `d ≤ k`; use `·` focusing bullets across `constructor` to avoid branch-tangle; rewrite differences explicitly (`have e : ... = 2 := by ring; rwa [e]`) rather than fishing with `ring_nf`.
- new tools added: `zify`, `lift`, `norm_cast`, `push_cast`, `exact_mod_cast`, `assumption_mod_cast`, `dvd_sub`, `Int.le_of_dvd`, `⟨witness, by ring⟩` divisibility pattern

## 13-06-2026 (Saturday, Week 5.5)
- Section 15 Sheet 2 `lemma1` (`x-3 ∣ x³-3 ↔ x-3 ∣ 24`) complete; skipped the optional 16-element enumeration (Buzzard-flagged CS grind).
- Difference-trick over ℤ: `x-3 ∣ x³-27` via `⟨x²+3x+9, by ring⟩` (cofactor is `x²+3x+9`, not `x²+x+9`), then transfer with `dvd_sub`/`dvd_add` + `rwa [key]` where `key : … = 24` / `= x³-3` is proved by `ring`. Hoist the shared `x³-27` divisibility above `constructor`.
- Debugging lesson: InfoView "No goals" + red squiggles ≠ done — Lean recovers from per-tactic errors and reaches an empty goal state with an invalid proof. Clear every red.
- Reinforced: `·` focusing bullets per `↔` direction; a divisibility `calc` can't silently switch to `=` mid-chain — `rwa [key]` instead.
- new tools added: `dvd_add`, `rwa [key]` difference-rewrite pattern

## Week 5 summary
- Strand A launched: `lean_buzzard` repo set up; Section 5 (groups) completed in full (Sheets 1-3) in 3 study days.
- Groups: Mathlib group API + axiom `rw`; own typeclass build (`WeakGroup`/`BadGroup`, left⟹right bootstrap, `decide` counterexample); subgroups + homs (`refine ?_`, dot-notation misbinding rule).
- Section roadmap corrected from repo tree: no quotients/modules sections. High-fit = 15 numberTheory, 14 UFDs/PIDs, 16 commutativeAlgebra, 19 algebraicNumberTheory, 21 galoisTheory.
- Section 15 (Number Theory) started, Sheets 1-2: casting toolkit (`norm_cast`/`push_cast`/`zify`/`lift`/`*_mod_cast`); divides-the-difference over ℕ (via `zify`) and ℤ; idioms `⟨witness, by ring⟩`, `Int.le_of_dvd`, `dvd_sub`/`dvd_add` + `rwa [key]`.
- Pace: 5 sheets across 2 sections vs ~1-sheet/week baseline. Well ahead; sheets so far lower-difficulty. Debug rule banked: "No goals" + red squiggles ≠ valid proof.

## Week 5 summary
- Strand A launched: `lean_buzzard` repo set up; Section 5 (groups) completed in full (Sheets 1-3) in 3 study days.
- Groups: Mathlib group API + axiom `rw`; own typeclass build (`WeakGroup`/`BadGroup`, left⟹right bootstrap, `decide` counterexample); subgroups + homs (`refine ?_`, dot-notation misbinding rule).
- Section roadmap corrected from repo tree: no quotients/modules sections. High-fit = 15 numberTheory, 14 UFDs/PIDs, 16 commutativeAlgebra, 19 algebraicNumberTheory, 21 galoisTheory.
- Section 15 (Number Theory) started, Sheets 1-2: casting toolkit (`norm_cast`/`push_cast`/`zify`/`lift`/`*_mod_cast`); divides-the-difference over ℕ (via `zify`) and ℤ; idioms `⟨witness, by ring⟩`, `Int.le_of_dvd`, `dvd_sub`/`dvd_add` + `rwa [key]`.
- Pace: 5 sheets across 2 sections vs ~1-sheet/week baseline. Well ahead; sheets so far lower-difficulty. Debug rule banked: "No goals" + red squiggles ≠ valid proof.


## 15-06-2026 (Monday, Week 6.1)
- Section 15 Sheet 3 (Sierpinski #3: infinitely many n with 5,13 ∣ 4n²+1) complete.
- `divides_of_cong_four` two ways: witness `⟨3380t²+416t+13, by ring⟩` / `⟨1300t²+160t+5, by ring⟩`; ZMod route `rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]; push_cast; ring_nf; reduce_mod_char`. Lesson: `ring_nf` leaves coefficients un-reduced mod n, so `decide` fails on free vars — `reduce_mod_char` reduces coeffs in `ZMod n` and finishes.
- `arb_large_soln`: direct construction, NOT induction — `intro N; use 65*(N+1)+4; constructor; omega; apply divides_of_cong_four` (`apply` infers `t := N+1` by unification).
- `infinite_iff_arb_large` (Buzzard's fiddly set-theory bridge): `Set.Infinite` is defeq `¬ S.Finite` — `apply hS` turns `False` into `S.Finite`. Fwd: bounded ⟹ `S ⊆ Set.Iic N`, finite via `Set.finite_Iic` + `Set.Finite.subset`. Rev: `hfin.bddAbove` gives `b ∈ upperBounds S`, applied as function `hb hnS : n ≤ b`, contradict via `omega`.
- `Set.Iic a` = {x | x ≤ a} = (-∞,a]. Ixx naming: I + left(i/o) + right(i/o/c), i=infinite o=open c=closed → Iic/Ici/Iio/Ioi/Icc/Ico/Ioc/Ioo. `Set.` and `Finset.` versions both exist. Find lemmas via `Set.finite_`+autocomplete, `exact?`, or Loogle.
- `obtain ⟨b, hb⟩ := hfin.bddAbove` and `obtain ⟨n, hn, hnS⟩ := h b` — destructure existentials/conjunctions inline.
- `push_neg` only pushes through connectives (¬∀/¬∃/¬∧/¬¬), NOT atomic negations like `¬(x ≤ N)` — use `rw [not_le]` or just `omega`.
- new tools added: `Set.Iic`/`Ixx` family, `Set.finite_Iic`, `Set.Finite.subset`, `BddAbove`/`upperBounds` (apply as function), `Set.Finite.bddAbove`, `reduce_mod_char`, `obtain`, `not_le`


## Week 6 summary
- One study day (6.1); busy week otherwise, tracks paused guilt-free per schedule.
- Section 15 Sheet 3 (Sierpinski #3) complete: ZMod modular arithmetic (`reduce_mod_char`), direct-construction existence proof, and the `Set.Infinite ↔ ∀ N ∃ n > N` bridge (`Set.Iic`/`finite_Iic`/`Finite.subset`, `BddAbove`/`upperBounds`).
- New API consolidated: `ZMod` divisibility, `Ixx` interval naming scheme, `Set.Finite` toolkit, `obtain`, `reduce_mod_char`.
- Pace: 1 sheet this week (= baseline) due to time; still well ahead cumulatively (Section 5 complete + Section 15 Sheets 1-3).

---

# Tactics / lemma glossary

Running list of tactics and Mathlib lemmas met in Strand A — new relative to MIL,
or worth re-noting. Depth tags: **[fluent]** / **[seen]** / **[shaky]** / **[to learn]**.

- `refine` **[to learn]** — like `apply` but lets you leave named holes `?_` to discharge as separate goals (partial term-mode). Section 5 Sheet 3.

- **Name it to reuse it** — an anonymous `example` binds no name, so nothing
  downstream can reference it. To reuse a result, promote it to a named
  `theorem`/`lemma`. When the declaration's type-variables are *explicit*
  (Buzzard's `variable (G : Type)`), pass instantiations by name —
  `lemma_name (a := 1) (b := 1)` — so Lean infers the rest from the goal
  instead of demanding `G` positionally.
- `inv_eq_iff_mul_eq_one` — `a⁻¹ = b ↔ a * b = 1`. Note Mathlib often orients
  the iff opposite to your hand-built version, so check direction before
  reaching for `.mp`/`.mpr`. `exact?` surfaces it.
- Group axioms in this pinned Mathlib use `_self` naming: `inv_mul_self`
  (`a⁻¹*a=1`), `mul_inv_self` (`a*a⁻¹=1`), alongside `mul_assoc`, `one_mul`,
  `mul_one`. `inv_one` for `(1)⁻¹=1`. `group` closes any axiom-only identity.

---

# Parking lot

- Confirm the inverse-axiom name in the pinned Mathlib (`mul_left_inv` vs `inv_mul_cancel`) — surfaces on Sheet 1.
- Learn the `refine ?_` mechanic properly — Sheet 3.
- Structure/class internals: groups/subgroups/homs are one-constructor inductive types. Sheet 2 forces a closer look at typeclasses (flagged in MIL handoff as used-but-not-deeply-understood).
- (cross-repo) The §5.3 mod-4 prime variant redo lives in `lean_learning`, not here.

---

# Mathlib observations (Strand B lurking)

Background only (≤30 min/week, Sunday scan): merged PRs in `NumberTheory/`,
`AlgebraicGeometry/`, `RingTheory/`, `FieldTheory/`; contributing + style-guide
notes; Zulip items worth remembering; exemplar contributors' PRs for style.

- (none yet)
