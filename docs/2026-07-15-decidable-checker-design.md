# ARCHIVED — 2026-07-15 — `Maybe` → `Dec` for `Definitions/TypeChecker.agda`

> Historical record. The checker it plans was replaced twice; the module it
> names no longer exists. Superseded by `Check/Alg.agda`. Do not work from
> this file.

Goal (unchanged): `check : ∀ Γ Δ P Pr s → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)` over a
finite graph LTS, and `Dec (⊢s M ∶ s)`, replacing the `Maybe` checker.

This is a **revision** of the original plan.  Phases 0–3 of v1 are done and
kept (see "What is done" below).  The remaining work — the completeness
capstone — is restructured: v1's §5 cost measure (C1–C4), §6 revisit
normalization, round-tree canonicalization, and budget arithmetic over
declarative derivations are **all deleted** and replaced by two much more
mechanical theorems.  Nothing already merged changes; `Alg`, `SemSkipP`,
`theoremB`, `spine`, `HasMainLeaf`, `Anc`, `skip-na` are all reused.

---

## 0. Why v1's remaining part was hard, and the two fixes

v1 proved completeness by strong induction on a `cost` measure because two
recursions were not structural:

1. **`~`-transported derivations.**  Theorem A's `~`-jumps replace leaf
   derivations by `td/bisim`-images, which are not subterms; recursing on them
   needed C2 (`cost` invariance under `td/bisim`) — the item that was stuck.
2. **Unbounded round chains.**  `t/unskip` traces and nested `t/skip` rounds
   are not bounded by the *derivation's* structure relative to `Pr`, so hitting
   the fixed budget `F Pr = suc (size G) * processFuel Pr` needed trace
   shortening (C3), revisit normalization (C4/§6.2) and per-chain budget
   arithmetic (§6.3) — derivation surgery, the most error-prone kind of Agda.

**Fix 1 (kills C2, C4, §6.2): quantify the completeness statement over `~`.**

```
complete : (D : Γ & Δ ⊢p P ◂ Pr ∶ s)
         → ∀ {δ′?no—same δ} {Δ′ : Vec (State G) δ} {s′}
         → Δ ~ᵛ Δ′ → s ~ s′
         → Alg (F Pr) Γ Δ′ P Pr s′
```

Because the induction hypothesis already covers *every* `~`-image of every
subderivation, we never recurse on a transported derivation.  Concretely, the
`t/skip` case instantiates Theorem A's leaf set with

```
L t = ∃[ ℓ ] Σ (HasMainLeaf std ℓ) (λ _ → ℓ ~ t)
```

whose `~`-closedness is literally `~trans`, and whose "main leaves ⊆ L" is
literally `(ℓ , hml , ~refl)`.  C2's entire purpose disappears.  Each case of
`complete` mirrors the corresponding case of `td/bisim` (`Safety/Skip.agda`
lines 152–196), which is the already-compiled template for how `~L→ / ~R→ /
~L→~ / ~R→~ / lookup/~ᵛ / ∈~ / skip/bisim` handle each constructor.

**Fix 2 (kills C1, C3, §6.1, §6.3, and the whole `cost` measure): a
saturation theorem on the `Alg` side.**

```
sat : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) P (Pr : Proc γ δ) s k
    → Alg k Γ Δ P Pr s → Alg (F Pr) Γ Δ P Pr s
```

`Alg (suc k) = Φ (Alg k)` for a monotone operator `Φ` (that is exactly what
`alg-mono`'s step case proves).  For fixed `Γ Δ P Pr`, the round components
(`pred`, `SemSkipP`) only move over `State G` — a finite set — so the Kleene
chain of `Φ` stabilizes within `size G` steps by pigeonhole on the *existing*
`wt / Incl / wt/strict / wt-bound` machinery in `LTS/Reachability.agda`.  The
proof lives entirely on the algorithmic side: no declarative derivations, no
bisimilarity, no surgery.  With `sat` in hand, `complete` needs **no fuel
bookkeeping at all**: every case builds `Alg (suc (F …))`-ish values and
immediately re-compresses with `sat`; `t/unskip` folds its trace one `pred`
step at a time with `sat` after each step, so traces never need shortening.

Everything else (Theorem A's walk, the top level) stays, and Theorem A's walk
is *simpler* than v1 planned: it is structural on the `PathViaP` path (§A).

---

## 1. What is done and stays (v1 Phases 0–3; build green)

* Phase 0 mechanical `Dec`s; `⊢e-unique`; exact `∈T?` for `t/end`.
* `LTS/Reachability.agda`: `reachVia`/`reachVia?`/`PathVia`/`PathViaP` +
  bridges, `wt`/`Incl`/`wt/mono`/`wt/strict`/`wt-bound`/`wt-full`,
  `≡true→T`/`T→≡true`.
* `SemSkipP`/`NLP`/`ReachLP`, `SkipDecide.semSkip?`, `SkipSem.theoremB`
  (the constructor direction, with `skip/cycle` closure) — the line-430
  incompleteness of the old `checkSkip` is already fixed.
* `Alg` (fuel-recursive **function**, `Alg 0 = ⊥` — strict positivity),
  `checkWithFuelD`, `alg-sound`, `alg-mono`, `direct?`/`direct-sound`/
  `direct-mono`, `semSkipP-mono`, `reachLP-mono`.
* In `Definitions/TypeChecker/Complete.agda`: `HasMainLeaf`, `spine` (S1),
  `Anc`, `skip-na`.
* Keep for reference: the §3.2 counterexample comment (why naive `Ξ`-search
  is incomplete) — it documents why `SemSkipP` exists.

**Deleted by this revision** (remove from `Complete.agda` once Phase C
compiles; they are no longer on any critical path):
`maxWithMem`, `maxWithMem-lb`, `traceLen`, `cost`, `costSkip`,
`cost-unskip<`, `costSkip<skip`, `cost-main<skip`, `costSkip-child<`.
Also delete v1's planned-but-unwritten C2, C3, C4, §6.1–§6.4 — do not attempt
them.

Notation below: `F Pr = suc (size G) * processFuel Pr` (unchanged);
`Step s α t = BTheory._-<_>->_ (graphTheory G) s α t`.

---

## Phase S — saturation (`Definitions/TypeChecker/Saturate.agda`, new file)

Independent of everything else; do it first.  Imports only
`Definitions.TypeChecker` (open `Processes N`, `GraphChecker G wb`) — it does
NOT need `Safety.Skip`.  Wire a root import so `runall.sh` builds it.

### S.1 The sub-budget and the single arithmetic lemma

```
J : ∀ {γ δ} → Proc γ δ → ℕ
J Pr = suc (size G) * (processFuel Pr ∸ 1)
```

* `pf≥1 : ∀ Pr → 1 ≤ processFuel Pr` (immediate: every clause is `suc _` or `1`).
* **The** budget lemma, uniform over constructors (no per-case arithmetic):

  ```
  J+size≡F : ∀ Pr → suc (J Pr + size G) ≡ F Pr
  -- F Pr = sucG * pf = sucG * suc (pf ∸ 1) = sucG + sucG*(pf ∸ 1)
  --      = suc (size G + J Pr); finish with +-comm.  Uses pf≥1.
  ```
* Per-case subterm bounds (each a one-liner given `pf≥1` / `⊔`/`+` monotony):

  ```
  send:  F Pr′ ≡ J (Q ! i < E >∙ Pr′)                     (pf ∸ 1 = pf Pr′)
  recv:  F (lookup Br j) ≤ J (Σ P ？[ S ]· Br)             (needs branchFuel-lb)
  if:    F Pr₁ ≤ J …  and  F Pr₂ ≤ J …                     (pf₁ ≤ pf₁ + pf₂)
  rec:   F Pr′ ≡ J (rec Pr′)
  v/∅:   J = 0 (Direct’s v/∅ cases don’t mention L, nothing needed)
  ```

  with `branchFuel-lb : ∀ {I} (Br : Vec (Proc γ δ) (suc I)) j →
  processFuel (lookup Br j) ≤ branchesFuel Br` (induction on `j`/`Br`).

### S.2 The level iteration `It` and its decision

For **arguments** (not module parameters) `{γ δ} Γ Δ P Pr` — fixed within one
level; only `s` varies:

```
It : ∀ {γ δ} → Vec Sort γ → Vec (State G) δ → Part → Proc γ δ
   → ℕ → State G → Set
It Γ Δ P Pr zero    s = ⊥
It Γ Δ P Pr (suc j) s =
    Direct (Alg (J Pr)) Γ Δ P Pr s                                   -- D₀, constant in j
  ⊎ (Σ[ r ∈ State G ] Incoming P s (edges G r) × It Γ Δ P Pr j r)   -- pred
  ⊎ SemSkipP (It Γ Δ P Pr j) P s                                    -- skip
```

Same fuel-recursive-function discipline as `Alg` (strict positivity: the
`SemSkipP` premise mentions `¬ It j` inside `PathViaP`, fine for a function
on `j` — same reason `Alg` is a function, see the memory note).

```
It? : ∀ … j s → Dec (It … j s)
  -- j = 0: no λ()
  -- suc j: direct? (Alg (J Pr)) (checkWithFuelD (J Pr)) … ⊎-dec
  --        (Fin.any? λ r → findIncoming P s (edges G r) ×-dec It? … j r) ⊎-dec
  --        SkipDecide.semSkip? (It … j) (It? … j) P s
It-mono : ∀ j → It … j s → It … (suc j) s
  -- induction on j; pred: recurse; skip: semSkipP-mono; D₀: id.
```

`×-dec/⊎-dec/→-dec/¬?` are currently `private` in `TypeChecker.agda` — either
un-private them or copy the 12 lines.

### S.3 Pigeonhole: the chain collapses within `size G` steps

```
stab? : ∀ j → Dec (∀ s → It … (suc j) s → It … j s)
stab? j = Fin.all? λ s → It? … (suc j) s →-dec It? … j s

findStab : Σ[ j ∈ ℕ ] j ≤ size G × (∀ s → It … (suc j) s → It … j s)
```

Search `j = 0, 1, …`; a failing `j` yields `s₀` with `It (suc j) s₀ × ¬ It j s₀`,
hence for the mark vectors `vec j = tabulate (λ s → ⌊ It? … j s ⌋)`:
`Incl (vec j) (vec (suc j))` (from `It-mono` + `fromWitness/toWitness`
plumbing, exactly like `mem→marked/marked→mem` in `SkipSem`) and
`vec j ≢ vec (suc j)` (lookup differs at `s₀`), so `wt` strictly grows
(`wt/strict`).  Implement as fuel-with-invariant recursion — the same pattern
as `SkipSem.build`'s `fresh`/`fullEq` (`TypeChecker.agda:617–640`): carry
`o : ℕ` with `size G ≤ wt (vec j) + o`; at `o = 0` the vector is full
(`wt-full`) and the next step cannot add anything, so `stab? j` cannot fail —
discharge with `⊥-elim` from the failing witness.  (Alternative bookkeeping:
`j + wt-deficit`; pick whichever invariant lands first, the `build` one is
proven-out.)

```
collapse : ∀ {j} → (∀ s → It … (suc j) s → It … j s)
         → ∀ d s → It … (j + d) s → It … j s
  -- induction on d: It (j + suc d) = Φ (It (j + d)) ⊆ Φ (It j) = It (suc j) ⊆ It j,
  -- where "Φ ⊆" is the same 3-case map as It-mono (pred recurse, semSkipP-mono, D₀ id).
itCap : ∀ k s → It … k s → It … (findStab .j) s
  -- k ≤ j : It-mono iterated; k > j : collapse with d = k ∸ j (m+[n∸m]≡n).
```

### S.4 Back into `Alg`

```
It→Alg : ∀ j s → It … j s → Alg (J Pr + j) Γ Δ P Pr s
  -- induction on j (+-suc rewrites):
  --   D₀:  direct-mono (alg-mono (≤ J+j)) → inj₁
  --   pred: IH → inj₂ (inj₁ …)
  --   skip: semSkipP-mono IH → inj₂ (inj₂ …)
```

### S.5 The mutual block

```
mutual
  sat : ∀ {γ δ} Γ Δ P (Pr : Proc γ δ) s k
      → Alg k Γ Δ P Pr s → Alg (F Pr) Γ Δ P Pr s
  sat Γ Δ P Pr s k a =
    alg-mono (≤ via J+size≡F and findStab .j ≤ size G)
      (It→Alg _ _ (itCap k s (algk→It Γ Δ P Pr k s a)))

  -- Alg k ⊆ It k at the same level; the ONLY place the structural
  -- recursion on Pr enters (through directSat).
  algk→It : ∀ {γ δ} Γ Δ P Pr k s → Alg k Γ Δ P Pr s → It Γ Δ P Pr k s
  algk→It … (suc k) s (inj₁ d)                    = inj₁ (directSat … d)
  algk→It … (suc k) s (inj₂ (inj₁ (r , inc , a))) =
    inj₂ (inj₁ (r , inc , algk→It … k r a))
  algk→It … (suc k) s (inj₂ (inj₂ sem))           =
    inj₂ (inj₂ (semSkipP-mono (λ {u} → algk→It … k u) sem))

  -- Direct (Alg k) ⊆ Direct (Alg (J Pr)): by cases on Pr, calling sat at
  -- the *visible* subterms.  Do NOT use direct-mono here — its `mp` is
  -- quantified over arbitrary Pr and would wreck termination.
  directSat : ∀ {γ δ} Γ Δ P Pr {k} s
            → Direct (Alg k) Γ Δ P Pr s → Direct (Alg (J Pr)) Γ Δ P Pr s
  -- send:  (S , t , etd , gr , a) ↦ (… , alg-mono (F Pr′ ≤ J) (sat … Pr′ t k a))
  -- recv:  (rw , all) ↦ (rw , All.map (λ f {j}{U} eq →
  --            alg-mono (F (lookup Br j) ≤ J) (satBr Br j … (f eq))) all)
  -- if:    both components via sat; rec: via sat; v/∅: id.

  -- vector companion so `lookup Br j` is structural
  satBr : ∀ {γ δ I} (Br : Vec (Proc γ δ) I) (j : Fin I) … k
        → Alg k … (lookup Br j) … → Alg (F (lookup Br j)) … (lookup Br j) …
  satBr (Pr ∷ Br) zero    = sat … Pr …
  satBr (Pr ∷ Br) (suc j) = satBr Br j
```

Termination: size-change — the cycle `sat → algk→It → directSat → sat/satBr`
strictly decreases `Pr`; the cycle `algk→It → algk→It` (pred case, and under
`semSkipP-mono`'s lambda) decreases `k` at equal `Pr`.  Calls under lambdas
are fine because their *arguments* are visibly smaller; what would break is
passing the unapplied recursive function (which is why `direct-mono` must not
be used here).  Keep all four in ONE mutual block; keep `It`/`It?`/`It-mono`/
`findStab`/`collapse`/`It→Alg` outside it (they never call `sat`).

Deliverable of Phase S: `sat` type-checks and `runall.sh` is green.
Estimated ~400–500 lines, all mechanical.

---

## Phase T — `~`-transport pack (`Complete.agda`)

Small standalone lemmas; all raw material is in scope via
`open Typing.MPST wb` (`~L→ ~R→ ~L→~ ~R→~ ~trans ~sym ~refl ~ᵛ-refl ~ᵛ/∷
lookup/~ᵛ ∈~`) and `SK = Safety.Skip wb` (`skip/bisim`, `skip-td/bisim`,
`skip/weaken-visited`).

```
-- T1: pull a filtered path back along ~ (right-to-left), for semSkipP-bisim
pathViaP-pull :
  (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′) → s ~ s′
  → PathViaP G (λ u → ¬ L u) s′ t′
  → ∃[ t ] PathViaP G (λ u → ¬ L u) s t × t ~ t′
  -- nil: (s , pathP/nil , s~s′)
  -- cons ¬Ls′ gr′ rest: gr = ~R→ s~s′ gr′ ; u~u′ = ~R→~ s~s′ gr′ ;
  --   ¬L s = λ Ls → ¬Ls′ (Lcl Ls s~s′) ; recurse on rest with u~u′.

-- T2: push an unfiltered path forward along ~, for ReachLP
pathVia-push :
  t ~ t′ → PathVia G (λ _ → true) t ℓ n
  → ∃[ ℓ′ ] PathVia G (λ _ → true) t′ ℓ′ n × ℓ ~ ℓ′
  -- nil: (t′ , path/nil , t~t′); cons: ~L→ / ~L→~, recurse.

-- T3: inactivity along ~ (one-liner)
na-~ : t ~ t′ → P not-active-in t → P not-active-in t′
na-~ t~t′ na = λ gr′ → na (~R→ t~t′ gr′)

-- T4: the composite — SemSkipP is ~-invariant for ~-closed L
semSkipP-bisim :
  (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)
  → s ~ s′ → SemSkipP L P s → SemSkipP L P s′
  -- given (path′ , ¬Lt′) at t′: T1 gives t, path, t~t′ (¬L t via Lcl contrapositive);
  -- sem t (path , ¬Lt) = (na , (ℓ , (n , p) , Lℓ));
  -- return (na-~ t~t′ na , (ℓ′ , (n , pathVia-push …) , Lcl Lℓ (from p’s ℓ~ℓ′))).

-- T5: main leaves of a transported skip tree come from ~-related leaves
hml-bisim :
  ∀ (D : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ H) (Δ~ : Δ ~ᵛ Δ′) (Ξ~ : Ξ ~ᵛ Ξ′) (H~ : H ~ H′)
  → HasMainLeaf (SK.skip-td/bisim Δ~ Ξ~ H~ D) ℓ′
  → ∃[ ℓ ] HasMainLeaf D ℓ × ℓ ~ ℓ′
  -- Case on D (the transported tree then REDUCES, so the hml match is definitional):
  --   skip/main td  : transported = skip/main (td/bisim …); hml = hml/main; ℓ = H, H~.
  --   skip/step …   : transported ktd gr″ .proj₂ = skip-td/bisim … (ktd (~R→ H~ gr″) .proj₂);
  --                   hml/step gr″ hml′ → IH on (ktd (~R→ H~ gr″) .proj₂) →
  --                   wrap with hml/step (~R→ H~ gr″).
  --   skip/cycle …  : transported = skip/cycle; no HasMainLeaf constructor — absurd.

-- T6: weaken the visited vector by a whole prefix (iterate Safety.Skip’s
-- single-insertion lemma at the FRONT, avoiding take/drop lemmas entirely)
weakenTo :
  ∀ (X : Fin ξ) (Ξ : Vec (State G) ξ)
  → Γ & Δ & dropSuc X Ξ ⊢skip[ m ] P ◂ Pr ∶ H
  → Γ & Δ & Ξ            ⊢skip[ m ] P ◂ Pr ∶ H
  -- recursion on X: zero, Ξ = y ∷ Ξ′ : skip/weaken-visited {Ξ′ = []} inserts y;
  -- suc X, Ξ = y ∷ Ξ′ : recurse to get over Ξ′, then insert y at the front.
  -- (dropSuc X Ξ = Data.Vec.drop-style tail after position X; define by the
  -- same recursion so no stdlib take/drop lemma is needed.)
```

---

## Phase A — Theorem A: the walk (finish; `Complete.agda`)

Statement (abstract in `L`, as already designed; instantiated by Phase C):

```
theoremA :
  (L : State G → Set)
  (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)                 -- ~-closed
  (std : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s)
  (lc  : ∀ {ℓ} → HasMainLeaf std ℓ → L ℓ)                -- leaves ⊆ L
  → SemSkipP L P s
```

`SemSkipP L P s = ∀ t → PathViaP (¬L) s t × ¬ L t → na t × ReachLP L t`, so
unfold and run the generalized walk.  **The walk is structural induction on
the `PathViaP` argument** — `PathViaP` carries no length index and none is
needed; the `~`-jump replaces the *carried tree*, never the recursion target.
This is strictly simpler than v1's "induction on k with Anc" sketch.

Strengthen `Anc` to carry leaf coverage (small refactor of the existing ✅):

```
AncL : (L : State G → Set) → ∀ {ξ} → Vec (State G) ξ → Set
AncL L []      = ⊤
AncL L (r ∷ Ξ) =
  (Σ[ D ∈ Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ r ]
     (∀ {ℓ} → HasMainLeaf D ℓ → L ℓ))
  × AncL L Ξ

ancLookup : AncL L Ξ → ∀ X →
  Σ[ D ∈ Γ & Δ & dropSuc X Ξ ⊢skip[ prod ] P ◂ Pr ∶ lu Ξ X ]
    (∀ {ℓ} → HasMainLeaf D ℓ → L ℓ)
  -- positional recursion on X / Ξ.
```

The walk:

```
walk :
  ∀ {ξ} {Ξ : Vec (State G) ξ} {r}
    (D   : Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ r)
    (anc : AncL L Ξ)
    (lc  : ∀ {ℓ} → HasMainLeaf D ℓ → L ℓ)
    {t} (path : PathViaP G (λ u → ¬ L u) r t) (¬Lt : ¬ L t)
  → (P not-active-in t) × ReachLP L t
```

* **`path = pathP/nil`** (so `r = t`):
  - `D = skip/main leaf` is absurd: `lc (hml/main leaf) : L t` vs `¬Lt`
    (this is exactly `skip-na` ✅ — reuse/adapt it).
  - `D = skip/step gr na ktd prf`: `na` answers the first component; `spine D`
    ✅ gives `(ℓ , (n , p) , hml)`; `ReachLP` = `(ℓ , (n , p) , lc hml)`.
* **`path = pathP/cons ¬Lr gr_β rest`** with `gr_β : Step r β u`:
  - `D = skip/main leaf` absurd via `lc`/`¬Lr` as above.
  - `D = skip/step gr na ktd prf`: inspect `ktd gr_β` **with the equation
    kept** — use the `go (ktd gr_β) refl` where-helper pattern (the exact
    with-abstraction gotcha and its fix are documented in `spine`,
    `Complete.agda:208–219`).  Let `anc′ = ((D , lc) , anc) : AncL L (r ∷ Ξ)`.
    * `(prod , child)` — descend:
      `walk child anc′ (λ hml → lc (hml/step gr_β hml†)) rest ¬Lt`,
      where `hml†` is `hml` transported along the kept equation
      `ktd gr_β ≡ (prod , child)` (a `subst`, same as in `spine`).
    * `(nonprod , child)` — `child` can only be `skip/cycle {X} eq` with
      `eq : lu (r ∷ Ξ) X ~ u` (`skip/main`/`skip/step` are `prod`).  **Jump**:
      1. `(D_a , lc_a) = ancLookup anc′ X` — a `prod` tree at `a = lu (r ∷ Ξ) X`
         over `dropSuc X (r ∷ Ξ)`;
      2. `D_w = weakenTo X (r ∷ Ξ) D_a` — same tree over `r ∷ Ξ` (T6);
         its leaves are unchanged, so its coverage is still `lc_a`
         (`weakenTo` maps `skip/main td ↦ skip/main td`; if the termination
         checker wants it, prove the 10-line
         `hml-weaken : HasMainLeaf (weakenTo …) ℓ → HasMainLeaf D_a ℓ`);
      3. `D_u = SK.skip-td/bisim ~ᵛ-refl ~ᵛ-refl eq D_w` — a `prod` tree
         **at `u`** over `r ∷ Ξ`;
      4. its coverage: `lc_u hml′ = Lcl (lc_a (hml-bisim … hml′ .proj₂ .proj₁ …)) (…~…)`
         — i.e. T5 recovers an original leaf `ℓ₀ ~ ℓ′`, `lc_a` puts `ℓ₀ ∈ L`,
         `Lcl` closes to `ℓ′`;
      5. continue: `walk D_u anc′ lc_u rest ¬Lt` — the path shrank, recursion
         is structural.  ✓

Then `theoremA L Lcl std lc t (path , ¬Lt) = walk std tt lc path ¬Lt`.

Notes:
* Everything `skip-td/bisim` needs (`Ξ ~ᵛ Ξ′` at equal length) is satisfied
  with `~ᵛ-refl`.
* The walk never inspects `Δ`; `Γ Δ P Pr` are module-fixed.
* v1's worry "the ancestor is bigger so induction on the derivation fails" is
  moot: recursion is on `path`, the tree is just carried data.

---

## Phase C — completeness up to `~` (`Complete.agda`)

```
mutual
  complete :
    (D : Γ & Δ ⊢p P ◂ Pr ∶ s)
    → ∀ {Δ′ s′} → Δ ~ᵛ Δ′ → s ~ s′
    → Alg (F Pr) Γ Δ′ P Pr s′

  completeLeaf :   -- extract-and-complete a main leaf, up to ~
    (D : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ r) {ℓ}
    → HasMainLeaf D ℓ
    → ∀ {Δ′ t} → Δ ~ᵛ Δ′ → ℓ ~ t
    → Alg (F Pr) Γ Δ′ P Pr t
```

Every case ends by injecting into `Alg (suc (F Pr))`-shaped data and calling
`sat` (Phase S) to come back to `Alg (F Pr)`; per-case fuel is *never*
tracked.  Useful case-local abbreviation:
`intoF : Alg (suc (F Pr)) … → Alg (F Pr) …` = `sat … (suc (F Pr))`.

Cases of `complete` (each mirrors the same constructor in `td/bisim`,
`Safety/Skip.agda:161–196` — keep it open as the template):

* `t/send gr etd td`, target `s′`:
  `gr′ = ~L→ s~s′ gr : Step s′ … t′`; IH `a = complete td Δ~Δ′ (~L→~ s~s′ gr)`
  at the *send subterm* `Pr₁`, giving `Alg (F Pr₁) … t′`;
  `inj₁ (S , t′ , etd , gr′ , alg-mono (F Pr₁ ≤ F Pr ∸ 1 …) a)`.
  Cleanest arithmetic: prove once `F-sub-send : suc (F Pr₁) ≤ F (Q ! i < E >∙ Pr₁)`
  (and siblings for recv/if/rec — reuse Phase S's per-case bounds:
  `F Pr₁ ≤ J Pr ≤ F Pr ∸ suc (size G)`), then inject at `suc (F Pr₁)` and
  finish with `alg-mono`.
* `t/recv gr conts`, target `s′`:
  - witness: `step⇒listed (~L→ s~s′ gr)` gives `RecvWitness … (edges G s′)`.
  - `All` over `edges G s′` by `All.tabulate λ {e} mem → λ {j}{U} eq → …`:
    from `eq`, `listed⇒step mem` is `Step s′ (P ⟶ Q # j < U >) t′`; pull back
    `gr₀ = ~R→ s~s′ (subst … eq (listed⇒step mem))`, `t₀~t′ = ~R→~ …`;
    IH `complete (conts gr₀) Δ~Δ′ t₀~t′ : Alg (F (lookup Br j)) (U ∷ Γ) Δ′ Q … t′`;
    `alg-mono` into the common bound.  (`conts gr₀` is a function-premise
    application — keep `conts` a pattern variable, the usual discipline.)
* `t/skip std`, target `s′` — the payoff case:
  ```
  L t          = ∃[ ℓ ] Σ (HasMainLeaf std ℓ) (λ _ → ℓ ~ t)
  Lcl          = λ (ℓ , hml , ℓ~t) t~t′ → (ℓ , hml , ~trans ℓ~t t~t′)
  lc           = λ hml → (_ , hml , ~refl)
  sem  : SemSkipP L P s   = theoremA L Lcl std lc                 (Phase A)
  sem′ : SemSkipP L P s′  = semSkipP-bisim Lcl s~s′ sem           (T4)
  L⊆   : ∀ {t} → L t → Alg (F Pr) Γ Δ′ P Pr t
       = λ (ℓ , hml , ℓ~t) → completeLeaf std hml Δ~Δ′ ℓ~t
  result = intoF (inj₂ (inj₂ (semSkipP-mono L⊆ sem′)))
  ```
* `t/unskip tr td` (`tr : H -[¬ P ]->* s`, `td` at `H`):
  `SK.skip/bisim s~s′ tr` gives `(H₀ , H~H₀ , tr′ : H₀ -[¬ P ]->* s′)`;
  IH `complete td Δ~Δ′ H~H₀ : Alg (F Pr) … H₀`; then fold, re-saturating at
  every step so no arithmetic ever appears:
  ```
  pred-fold : ∀ {a b} → a -[¬ P ]->* b → Alg (F Pr) Γ Δ′ P Pr a
            → Alg (F Pr) Γ Δ′ P Pr b
  pred-fold skip/refl            alg = alg
  pred-fold (skip/step gr P∉ tr) alg =
    pred-fold tr (intoF (inj₂ (inj₁ (_ , (_ , step⇒listed gr , P∉) , alg))))
  ```
  No trace shortening, no `traceLen`.
* `t/if etd ttd ftd`: two IHs at `s~s′`, `alg-mono` both into the common
  bound, `inj₁ (etd , _ , _)`, `intoF`.
* `t/rec mg td`: IH `complete td (~ᵛ/∷ s~s′ Δ~Δ′) s~s′ : Alg (F Pr₁) Γ (s′ ∷ Δ′) …`;
  `inj₁ (mg , alg-mono … it)`, `intoF`.
* `t/var eq`: `inj₁ (~trans (lookup/~ᵛ Δ~Δ′ _ eq) s~s′)` at fuel `1`,
  `alg-mono` to `F Pr`.  (Same expression as `td/bisim`'s `t/var` case.)
* `t/end done`: `inj₁ (done ∘ ∈~ (~sym s~s′))` at fuel `1`, `alg-mono`.

`completeLeaf` (structural on the tree, matching `D` and the `hml` together —
same index-matching style as `spine`):

* `D = skip/main leaf`, `hml = hml/main leaf` → `complete leaf Δ~Δ′ ℓ~t`.
* `D = skip/step gr na ktd prf`, `hml = hml/step gr′ hml′` →
  `completeLeaf (ktd gr′ .proj₂) hml′ Δ~Δ′ ℓ~t`.
* `skip/cycle`: no `hml` constructor — absurd pattern.

Termination: `complete (t/skip std)` calls `theoremA` (non-recursive) and
`completeLeaf std …`; `completeLeaf` descends the tree and at leaves calls
`complete` on a strict subterm — the same size-change shape `spine` already
passes.  No measure, no `cost`.

Finally:

```
complete₀ : (D : Γ & Δ ⊢p P ◂ Pr ∶ s) → Alg (F Pr) Γ Δ P Pr s
complete₀ D = complete D ~ᵛ-refl ~refl
```

---

## Phase F — top level (`TypeChecker.agda` + wrappers)

1. ```
   check : ∀ {γ δ} Γ Δ P Pr s → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
   check Γ Δ P Pr s with checkWithFuelD (F Pr) Γ Δ P Pr s
   ... | yes a = yes (alg-sound (F Pr) a)
   ... | no ¬a = no (¬a ∘ complete₀)
   ```
   Placement: `complete₀` lives in `Complete.agda` (needs `Safety.Skip`), so
   `check` must live there too (or in a new `Definitions/TypeChecker/Check.agda`
   importing `Complete`).  `Definitions.TypeChecker` itself keeps everything
   up to `alg-sound`; the aggregator stays acyclic exactly as now.
2. `checkClosed`, `checkSession : ∀ M s → Dec (⊢s M ∶ s)` — finite `∀` over
   `Fin N` (`allDec : (∀ i → Dec (A i)) → Dec (∀ i → A i)`; `no f = λ g → f (g i)`).
3. `checkProcess/checkSession/checkRooted*` to `Dec (CheckedProcess …)`:
   * `wellBehaved? G = no ¬wb`: refute the record's first field directly —
     `no λ (checkedProcess wb′ _) → ¬wb wb′`.  No lemma needed.
   * `yes wb` but `check = no ¬td`: this is the only place needing
     ```
     typing-wb-irrelevant :
       (wb wb′ : WellBehaved (graphTheory G)) →
       Typing.MPST wb′ ._&_⊢p_∶_ Γ Δ PPr s → Typing.MPST wb ._&_⊢p_∶_ Γ Δ PPr s
     ```
     Mechanical mutual induction (with the `⊢skip` judgment): every
     constructor field is `BTheory`-level (`_-<_>->_`, `~`, `∈T`,
     `not-active-in` are all derived from `B`, never from `wb`), so each case
     is a re-wrap.  ~100 lines.
4. Delete the `Maybe` cluster: `CheckFunction`, `checkContinuation(s)`,
   `checkDirect`, `checkPredecessor(s)`, `checkClosureSkip`, `checkClosure`,
   `checkWithFuel`, old `check`, `fromT`, `allParticipants`-Maybe.  Then
   delete the dead `cost` block from `Complete.agda` (list in §1) and the
   stale comments the old checker carried.

---

## Order of implementation (each step leaves `runall.sh` green)

1. **Phase S** (`Saturate.agda`) — fully independent, mechanical; do first.
   If any of S stalls, everything else still composes with `sat` as a
   module parameter, but S has no research risk: check S.1's `J+size≡F`
   numerically first (`size G = 2`, `pf = 3`: `F = 9`, `J = 6`, `suc (6+2) = 9` ✓).
2. **Phase T** — T1–T4 (needed by C), T5–T6 (needed by A).  ~150 lines.
3. **Phase A** — refactor `Anc → AncL`, write `ancLookup`, `weakenTo`, then
   the walk.  Keep `spine`/`skip-na` as is.
4. **Phase C** — `complete`/`completeLeaf`/`pred-fold`/`complete₀`, then the
   per-constructor `F`-bounds (share Phase S's S.1 lemmas — export them).
5. **Phase F** — `check`, session/top-level `Dec`s, `typing-wb-irrelevant`,
   delete the `Maybe` cluster and the dead cost block.
6. Update `status.md`; delete stale comments; final `runall.sh`.

## Gotchas carried forward (from status.md, still apply)

* Non-injective `wt/Incl/mark/lookup/tabulate`: pin vector implicits
  (`{Ξ}`, `{left}`, `{right}`) at call sites (bites again in S.3's `vec j`).
* `Alg`/`It` must be fuel-recursive *functions*, not datatypes (positivity).
* Function premises (`conts`, `ktd`) must stay clause pattern variables for
  termination (bites in C's recv case and A's walk).
* `with … in eq` dropping equations when context depends on `ktd gr`: use the
  `go (ktd gr) refl` where-helper (`spine` shows the working pattern; needed
  again in A's walk).
* In `Complete.agda`: `open Typing.MPST wb hiding (_,_)`; Vec's `_∷_/[]`;
  qualify `BTheory._-<_>->_ (graphTheory G)`; `skip/step`'s target implicit
  is `{G' = …}` (ASCII apostrophe).
* New: in Phase S never pass an unapplied recursive function into a
  higher-order lemma (`direct-mono`!) — inline per-case (`directSat`).

## Inventory delta vs v1

**Dropped entirely:** `cost`/`costSkip`, C1 lemma family, C2, C3, C4,
round-tree canonicalization (`skip/cat` collapsing), revisit normalization,
budget `B Pr h`, `maxWithMem(-lb)`, `traceLen`.

**New:** `sat` + `It` machinery (Phase S), transport pack T1–T6,
`AncL`/`ancLookup`/`weakenTo`, `walk`/`theoremA`, `complete`/`completeLeaf`/
`pred-fold`, `allDec`, `typing-wb-irrelevant` (was already planned).

**Reused as-is:** everything in v1's "Reused" list, plus (new since then)
`Alg`, `checkWithFuelD`, `alg-sound`, `alg-mono`, `direct?/direct-sound/
direct-mono`, `semSkipP-mono`, `reachLP-mono`, `SkipDecide.semSkip?`,
`SkipSem.theoremB`, `spine`, `HasMainLeaf`, `skip-na`, `skip/bisim`,
`skip-td/bisim`, `skip/weaken-visited`, `wt`-family, `PathVia(P)` bridges.
