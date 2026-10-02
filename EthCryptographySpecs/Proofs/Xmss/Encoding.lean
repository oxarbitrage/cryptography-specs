import EthCryptographySpecs.Xmss.Encoding
import Mathlib.Tactic

/-!
# Proofs: `Xmss.Encoding`

What an accepted encoding is, and what it guarantees.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

variable {pp : PublicParam} {msg : Message} {rnd : Randomness} {epoch : Epoch}
  {x : Vector (Fin CHAIN_LENGTH) V}

/-- Acceptance returns the digest's own digits. -/
theorem wotsEncode_eq_digits (h : wotsEncode pp msg rnd epoch = some x) :
    x = Internal.digits
      (tweakHash pp .encoding 0 epoch (encodingPayload msg rnd)) := by
  -- Only the accepting branch produces a result, and it returns the digits.
  simp only [wotsEncode] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h (by simp)

/-- An accepted encoding has both spare bits zero. -/
theorem padded_of_wotsEncode (h : wotsEncode pp msg rnd epoch = some x) :
    Internal.padded
      (tweakHash pp .encoding 0 epoch (encodingPayload msg rnd)) = true := by
  simp only [wotsEncode] at h
  split at h
  · simp_all
  · exact absurd h (by simp)

/-- An accepted encoding's digits sum to the target.

A fixed sum is what fixes the verifier's step count. -/
theorem sum_of_wotsEncode (h : wotsEncode pp msg rnd epoch = some x) :
    x.foldl (fun sum d => sum + d.val) 0 = TARGET_SUM := by
  simp only [wotsEncode] at h
  split at h
  · rename_i hcond
    obtain ⟨_, htarget⟩ := (Bool.and_eq_true _ _).mp hcond
    rw [← Option.some_inj.mp h]
    -- The narrow rewrite keeps the digest from being evaluated.
    simp only [Internal.onTarget, beq_iff_eq] at htarget
    exact htarget
  · exact absurd h (by simp)

/-! ## Digit sums -/

/-- The digit sum the specification folds is the sum over indices. -/
theorem digitSum_eq_sum (x : Vector (Fin CHAIN_LENGTH) V) :
    x.foldl (fun sum d => sum + d.val) 0 = ∑ i : Fin V, (x[i] : Nat) := by
  -- A vector fold is a fold over its list.
  have h1 : x.foldl (fun sum d => sum + d.val) 0
      = x.toList.foldl (fun sum d => sum + d.val) 0 := by
    obtain ⟨arr, harr⟩ := x
    simp [Array.foldl_toList]
  -- Adding the digit values is summing the mapped list.
  have h2 : x.toList.foldl (fun sum d => sum + d.val) 0
      = (x.toList.map Fin.val).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
  -- A vector is the tabulation of its entries, so that list sum is indexed.
  have h3 : (x.toList.map Fin.val).sum = ∑ i : Fin V, (x[i] : Nat) := by
    conv_lhs => rw [← Vector.ofFn_getElem (xs := x)]
    rw [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [h1, h2, h3]

/-! ## Digits determine the digest

The identity below is the one an aggregation circuit checks, one per half.

It holds only once the spare bit is zero, which is what the grinding buys. -/

/-- The low `k` base-`b` digits of a number reconstruct it modulo `b ^ k`. -/
theorem sum_base_digits_eq_mod (b n : Nat) : ∀ k : Nat,
    ∑ r ∈ Finset.range k, n / b ^ r % b * b ^ r = n % b ^ k := by
  intro k
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    -- One more digit is one more factor of the base in the modulus.
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ring

/-- A number below `b ^ k` is the sum of its `k` low base-`b` digits. -/
theorem eq_sum_base_digits {b n k : Nat} (hn : n < b ^ k) :
    n = ∑ r ∈ Finset.range k, n / b ^ r % b * b ^ r := by
  rw [sum_base_digits_eq_mod, Nat.mod_eq_of_lt hn]

/-- Shifting a word down by `3 * r` divides it by `8 ^ r`. -/
private theorem toNat_shiftRight_digit (w : UInt64) {r : Nat} (hr : r < 21) :
    (w >>> (3 * UInt64.ofNat r)).toNat = w.toNat / 8 ^ r := by
  rw [UInt64.toNat_shiftRight]
  -- The shift amount is below 64, so neither the wrap nor the mod bites.
  have h3 : (3 * UInt64.ofNat r).toNat = 3 * r := by
    rw [show (3 : UInt64) = UInt64.ofNat 3 from rfl, ← UInt64.ofNat_mul,
      UInt64.toNat_ofNat']
    omega
  rw [h3, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ (3 * r) = 8 ^ r by rw [pow_mul]; norm_num]

/-- A word whose top bit is clear is below `2 ^ 63`. -/
private theorem lt_two_pow_of_topBit_zero (w : UInt64)
    (h : (w >>> 63 == 0) = true) : w.toNat < 2 ^ 63 := by
  have hz : (w >>> 63).toNat = 0 := by simp_all
  have h63 : UInt64.toNat 63 % 64 = 63 := by decide
  rw [UInt64.toNat_shiftRight, h63, Nat.shiftRight_eq_div_pow] at hz
  have hw := w.toNat_lt
  omega

/-- Digit `r` of a word is its base-eight digit at position `r`. -/
theorem digit_val (w : UInt64) {r : Nat} (hr : r < 21) :
    (Internal.digit w r : Nat) = w.toNat / 8 ^ r % CHAIN_LENGTH := by
  show (w >>> (3 * UInt64.ofNat r)).toNat % CHAIN_LENGTH = _
  rw [toNat_shiftRight_digit w hr]

/-- An admissible half equals its digits weighted by powers of eight. -/
theorem digestWord_eq_sum_digits {d : Digest} (hp : Internal.padded d = true)
    (half : Fin 2) :
    (Internal.digestWord d half).toNat =
      ∑ r ∈ Finset.range (V / 2),
        (Internal.digit (Internal.digestWord d half) r : Nat)
          * CHAIN_LENGTH ^ r := by
  obtain ⟨h0, h1⟩ := (Bool.and_eq_true _ _).mp hp
  -- The spare bit being zero is what puts the half below 8 ^ 21.
  have hlt : (Internal.digestWord d half).toNat < 8 ^ 21 := by
    have h863 : (2 : Nat) ^ 63 = 8 ^ 21 := by
      norm_num [show (63 : Nat) = 3 * 21 from rfl, pow_mul]
    rw [← h863]
    fin_cases half
    · exact lt_two_pow_of_topBit_zero _ h0
    · exact lt_two_pow_of_topBit_zero _ h1
  rw [show V / 2 = 21 from rfl]
  conv_lhs => rw [eq_sum_base_digits hlt]
  -- Each summand is the same digit, read two ways.
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [digit_val _ (Finset.mem_range.mp hr)]
  rfl

/-- A verifier walks exactly 99 chain steps on an accepted encoding. -/
theorem chainSteps_of_wotsEncode {pp : PublicParam} {msg : Message}
    {rnd : Randomness} {epoch : Epoch} {x : Vector (Fin CHAIN_LENGTH) V}
    (h : wotsEncode pp msg rnd epoch = some x) :
    ∑ i : Fin V, (CHAIN_LENGTH - 1 - (x[i] : Nat)) = NUM_CHAIN_HASHES := by
  have hsum : ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
    rw [← digitSum_eq_sum]; exact sum_of_wotsEncode h
  -- Steps walked plus steps revealed is the full chain, digit by digit.
  have hpt : ∀ i : Fin V,
      (CHAIN_LENGTH - 1 - (x[i] : Nat)) + (x[i] : Nat) = CHAIN_LENGTH - 1 := by
    intro i
    have hb := (x[i]).isLt
    simp only [CHAIN_LENGTH, W] at hb ⊢
    omega
  have hfull : ∑ i : Fin V,
      ((CHAIN_LENGTH - 1 - (x[i] : Nat)) + (x[i] : Nat))
        = V * (CHAIN_LENGTH - 1) := by
    rw [Finset.sum_congr rfl fun i _ => hpt i]
    simp [Finset.sum_const, Finset.card_univ]
  -- So the walked steps are what the target sum leaves.
  rw [Finset.sum_add_distrib, hsum] at hfull
  simp only [V, CHAIN_LENGTH, W, TARGET_SUM, NUM_CHAIN_HASHES] at hfull ⊢
  omega

/-! ## Incomparability

Distinct codewords must each exceed the other somewhere.

Chains only ever walk forward.

So a signature for one codeword reaches another only if that one dominates it.

A constant digit sum rules that out. -/

/-- Pointwise domination with equal sums forces equality. -/
theorem eq_of_le_of_sum_eq {x y : Vector (Fin CHAIN_LENGTH) V}
    (hle : ∀ i : Fin V, (x[i] : Nat) ≤ (y[i] : Nat))
    (hsum : ∑ i : Fin V, (x[i] : Nat) = ∑ i : Fin V, (y[i] : Nat)) : x = y := by
  by_contra hne
  -- Unequal vectors differ at some index.
  obtain ⟨j, hj⟩ : ∃ j : Fin V, (x[j] : Nat) ≠ (y[j] : Nat) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (Vector.ext fun i hi => Fin.val_inj.mp (hall ⟨i, hi⟩))
  -- One strict index among weak ones makes the whole sum strict.
  have hlt : ∑ i : Fin V, (x[i] : Nat) < ∑ i : Fin V, (y[i] : Nat) :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hle j) hj⟩
  omega

/-- Two accepted encodings are equal, or each exceeds the other somewhere.

Neither can be reached from the other by walking chains forward. -/
theorem wotsEncode_incomparable
    {pp₁ pp₂ : PublicParam} {m₁ m₂ : Message} {r₁ r₂ : Randomness}
    {e₁ e₂ : Epoch} {x y : Vector (Fin CHAIN_LENGTH) V}
    (h₁ : wotsEncode pp₁ m₁ r₁ e₁ = some x)
    (h₂ : wotsEncode pp₂ m₂ r₂ e₂ = some y) (hne : x ≠ y) :
    (∃ i : Fin V, (x[i] : Nat) < (y[i] : Nat)) ∧
      (∃ i : Fin V, (y[i] : Nat) < (x[i] : Nat)) := by
  -- Acceptance pins both sums to the target, so the two sums agree.
  have hx : ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
    rw [← digitSum_eq_sum]; exact sum_of_wotsEncode h₁
  have hy : ∑ i : Fin V, (y[i] : Nat) = TARGET_SUM := by
    rw [← digitSum_eq_sum]; exact sum_of_wotsEncode h₂
  constructor
  -- Were one never to exceed the other, equal sums would make them equal.
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno (hy.trans hx.symm)).symm
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno (hx.trans hy.symm))

/-! ## The size of the code

A signer grinds randomizers until the digits land in the code.

How often that succeeds is set by one number: how many digit vectors sum to the target.

The specification note gives it as an inclusion-exclusion sum.

Here it is counted directly, by a table over bounded compositions, and the two agree. -/

/-- Digit strings of length `n`, each digit below `m`, summing to `s`.

The first digit is `d`, and the others sum to what it leaves. -/
def boundedCompositions (m : Nat) : Nat → Nat → Nat
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => ∑ d ∈ Finset.range m, if d ≤ s then boundedCompositions m n (s - d) else 0

/-- Counting digit strings is counting bounded compositions. -/
theorem card_sum_eq_boundedCompositions (m : Nat) : ∀ n s,
    (Finset.univ.filter fun f : Fin n → Fin m => ∑ i, (f i : Nat) = s).card
      = boundedCompositions m n s := by
  intro n
  induction n with
  | zero =>
    intro s
    by_cases h : s = 0 <;> simp [boundedCompositions, h, eq_comm]
  | succ n ih =>
    intro s
    -- Split a string into its first digit and the rest.
    rw [Finset.card_filter, ← (Fin.consEquiv fun _ => Fin m).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [boundedCompositions,
      ← Fin.sum_univ_eq_sum_range (fun d => if d ≤ s then boundedCompositions m n (s - d) else 0)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← ih, ← Finset.card_filter]
    -- The rest must sum to what the first digit leaves, if it leaves anything.
    split_ifs with hd
    · congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro g _
      omega

/-- One row of the table: counts for one more digit, at every sum up to `b`. -/
def compositionRow (m : Nat) (row : List Nat) (b : Nat) : List Nat :=
  (List.range (b + 1)).map fun s =>
    ((List.range m).map fun d => if d ≤ s then row.getD (s - d) 0 else 0).sum

/-- The table of bounded compositions, row `n` holding the counts for length `n`.

Each row is built from the one before, so the count takes `n` passes, not `m ^ n` cases. -/
def compositionTable (m b : Nat) : Nat → List Nat
  | 0 => (List.range (b + 1)).map fun s => if s = 0 then 1 else 0
  | n + 1 => compositionRow m (compositionTable m b n) b

private theorem list_sum_range (m : Nat) (f : Nat → Nat) :
    ((List.range m).map f).sum = ∑ d ∈ Finset.range m, f d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem getD_range_map {b s : Nat} (f : Nat → Nat) (hs : s ≤ b) :
    ((List.range (b + 1)).map f).getD s 0 = f s := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range (by omega : s < b + 1)]

/-- The table holds the bounded-composition counts. -/
theorem compositionTable_getD (m b : Nat) : ∀ n s, s ≤ b →
    (compositionTable m b n).getD s 0 = boundedCompositions m n s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rw [compositionTable, getD_range_map _ hs, boundedCompositions]
  | succ n ih =>
    intro s hs
    rw [compositionTable, compositionRow, getD_range_map _ hs, list_sum_range,
      boundedCompositions]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with hd
    · exact ih _ (by omega)
    · rfl

/-- The specification accepts exactly the digit vectors that sum to the target. -/
theorem onTarget_ofFn_iff (f : Fin V → Fin CHAIN_LENGTH) :
    Internal.onTarget (Vector.ofFn f) = true ↔ ∑ i, (f i : Nat) = TARGET_SUM := by
  simp only [Internal.onTarget, beq_iff_eq, digitSum_eq_sum, Fin.getElem_fin,
    Vector.getElem_ofFn]

/-- The code has `11539185377238682781344003244544752` codewords.

That is the number of ways 42 digits between 0 and 7 can sum to 195. -/
theorem card_code :
    (Finset.univ.filter fun f : Fin V → Fin CHAIN_LENGTH =>
      Internal.onTarget (Vector.ofFn f) = true).card
        = 11539185377238682781344003244544752 := by
  simp only [onTarget_ofFn_iff]
  rw [card_sum_eq_boundedCompositions,
    ← compositionTable_getD _ TARGET_SUM _ _ le_rfl]
  -- 42 passes over a table of 196 sums, evaluated by the kernel.
  decide +kernel

/-- The note's inclusion-exclusion count, term `b` correcting for `b` digits above 7.

Terms stop at `b = 24`, the last with `8 * b ≤ 195`. -/
theorem inclusionExclusion_eq :
    ∑ b ∈ Finset.range (TARGET_SUM / CHAIN_LENGTH + 1),
      (-1 : Int) ^ b * (V.choose b : Int)
        * ((TARGET_SUM - CHAIN_LENGTH * b + V - 1).choose (V - 1) : Int)
      = 11539185377238682781344003244544752 := by
  -- Falling factorials keep each binomial to 41 multiplications.
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- The code holds at least a `2 ^ -15` fraction of all digests.

A digest has 128 bits, and a padded digest is accepted exactly when its digits are a codeword.

So this is the note's bound on the chance that one grinding attempt is accepted. -/
theorem acceptance_ge :
    (2 : ℝ) ^ (-15 : ℤ) ≤
      ((Finset.univ.filter fun f : Fin V → Fin CHAIN_LENGTH =>
        Internal.onTarget (Vector.ofFn f) = true).card : ℝ) / 2 ^ 128 := by
  rw [card_code]
  norm_num

/-! ## Known answer

Pins the bit layout: which half a digit comes from, and where in that half. -/

/-- A digest whose 42 digits are spread across both halves and all widths. -/
theorem digits_known_answer :
    (Internal.digits
      ⟨#[0xfc, 0x04, 0x19, 0xbf, 0xf7, 0xd7, 0x8b, 0x7f,
         0xae, 0x81, 0x32, 0xe6, 0xed, 0xf6, 0x2b, 0x7f], rfl⟩).toList.map
        Fin.val =
      [4, 7, 3, 2, 0, 2, 6, 0, 7, 7, 6, 3, 7, 7, 5, 6, 3, 1, 6, 7, 7,
       6, 5, 6, 0, 0, 5, 4, 1, 6, 4, 7, 6, 6, 5, 5, 7, 3, 5, 4, 7, 7] := by
  decide +kernel

end EthCryptographySpecs.Xmss
