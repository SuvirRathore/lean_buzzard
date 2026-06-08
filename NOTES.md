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
