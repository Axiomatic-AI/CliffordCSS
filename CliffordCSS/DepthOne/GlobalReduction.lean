import CliffordCSS.DepthOne.LocalBlock
import CliffordCSS.DepthOne.TerminalFactor

/-!
# Global reduction, and Theorem D.1 conditional on Lemma D.4

Pure mathematics : **Lemma D.6 (Global reduction)** of *Beyond
transversality* (arXiv:2608.05688) and, assembling it with the terminal factorization, the
`⊆` direction of **Theorem D.1** — both **conditional on Lemma D.4 (Local reduction)**, which the
paper establishes by exhaustive computer verification of the `720 + 6` blocks and which is *not*
formalized here.

Nothing in this file is named Theorem D.1 unqualified: the headline result is
`fixedMatchingSlice_eq_sup_familyM_of_localReduction`, whose hypothesis is `LocalReduction 2 3` —
the width-two half of Lemma D.4 (the width-one half is proved, `localReduction_width_one`).
-/

open Matrix

namespace CliffordCSS

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}

/-! ### Manufacturing a global move out of the layer (Lemmas D.2 + D.5) -/

/-- **A `Z`-move manufactured from the layer itself.** For `G ∈ N_M` and a coefficient vector `ε`,
the diagonal circuit `U_Z(S^Z(G, ε))` of the manufactured parameter is a valid `M`-supported gate,
i.e. an element `U ∈ S^Z_M` (Lemma D.2), and multiplying `G` by it acts on **every** cell block
`g_𝔟` by the local circuit `U_Z(S^Z(g_𝔟, ε))` of the *same* `ε` (Lemma D.5). Steering one cell along
its path therefore drags the others, but by an explicitly known amount. -/
theorem exists_mem_shearZFamilyM_localBlock (hσ : Function.Involutive σ)
    {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) (ε : Fin 3 → ZMod 2) :
    ∃ U : ↥(binarySymplecticGroup ι), U ∈ shearZFamilyM C_X C_Z σ hσ ∧
      ∀ b : Finset ι, (∀ a ∈ b, σ a ∈ b) →
        localBlock b ((U * G : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
            = shearZ (layerZParam (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ε)
              * localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∧
        localBlock b ((G * U : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
            = localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
              * shearZ (layerZParam (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ε) := by
  have hGbd : IsSpBlockDiagonal σ (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :=
    (mem_fixedMatchingSlice_iff.mp hG).2
  have hSadm : layerZParam (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ε
      ∈ admissibleParamsBlockDiag C_X C_Z σ :=
    automaticParamsZ_le (Matrix.fromBlocks_toBlocks _).symm hG (spzParam_mem_span _ _ _ ε)
  obtain ⟨hSsymm, -, hScell⟩ := mem_admissibleParamsBlockDiag.mp hSadm
  refine ⟨⟨shearZ (layerZParam (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ε), shearZ_mem_iff.mpr hSsymm⟩,
    shearZ_mem_shearZFamilyM hσ hSadm rfl, fun b hb => ⟨?_, ?_⟩⟩
  · rw [Submonoid.coe_mul, localBlock_mul hb (shearZ_isSpBlockDiagonal hScell), localBlock_shearZ,
      layerZParam_localBlock hσ hb hGbd]
  · rw [Submonoid.coe_mul, localBlock_mul hb hGbd, localBlock_shearZ,
      layerZParam_localBlock hσ hb hGbd]

/-- **An `X`-move manufactured from the layer itself** (dual to
`exists_mem_shearZFamilyM_localBlock`): the diagonal circuit `L_X(S^X(G, ε))` lies in `S^X_M` and
acts on every cell block by `L_X(S^X(g_𝔟, ε))`. -/
theorem exists_mem_shearXFamilyM_localBlock (hσ : Function.Involutive σ)
    {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) (ε : Fin 3 → ZMod 2) :
    ∃ U : ↥(binarySymplecticGroup ι), U ∈ shearXFamilyM C_X C_Z σ hσ ∧
      ∀ b : Finset ι, (∀ a ∈ b, σ a ∈ b) →
        localBlock b ((U * G : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
            = shearX (layerXParam (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ε)
              * localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∧
        localBlock b ((G * U : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
            = localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
              * shearX (layerXParam (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ε) := by
  have hGbd : IsSpBlockDiagonal σ (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :=
    (mem_fixedMatchingSlice_iff.mp hG).2
  have hTadm : layerXParam (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ε
      ∈ admissibleParamsBlockDiag C_Z C_X σ :=
    automaticParamsX_le (Matrix.fromBlocks_toBlocks _).symm hG (spxParam_mem_span _ _ _ ε)
  obtain ⟨hTsymm, -, hTcell⟩ := mem_admissibleParamsBlockDiag.mp hTadm
  refine ⟨⟨shearX (layerXParam (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ε), shearX_mem_iff.mpr hTsymm⟩,
    shearX_mem_shearXFamilyM hσ hTadm rfl, fun b hb => ⟨?_, ?_⟩⟩
  · rw [Submonoid.coe_mul, localBlock_mul hb (shearX_isSpBlockDiagonal hTcell), localBlock_shearX,
      layerXParam_localBlock hσ hb hGbd]
  · rw [Submonoid.coe_mul, localBlock_mul hb hGbd, localBlock_shearX,
      layerXParam_localBlock hσ hb hGbd]

/-- **Every local move at a cell is realized by one global multiplication** — the `Z`/`X`-blind
packaging of `exists_mem_shearZFamilyM_localBlock` / `exists_mem_shearXFamilyM_localBlock` that the
reduction consumes. Given a move `g_𝔟 ↦ g'` of the move graph at a `σ`-closed cell `𝔟`, there is a
single generator `U` of `S^Z_M` or `S^X_M` such that

* multiplying `G` by `U` on the appropriate side takes the block at `𝔟` to `g'`, and
* **every already-terminal cell is left untouched**: on a terminal cell block all six manufactured
  parameters vanish (`spzParam_eq_zero_of_isTerminalBlock` and its `X` dual), so the induced local
  circuit is `U_Z(0) = I` there, on either side.

Both families and both sides are handled once here, so the reduction below need only distinguish
*left* from *right*. -/
theorem exists_mem_shearFamilyM_of_isBlockMove (hσ : Function.Involutive σ) {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b) {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) {g' : Matrix (b ⊕ b) (b ⊕ b) (ZMod 2)}
    (hmove : IsBlockMove (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) g') :
    ∃ U : ↥(binarySymplecticGroup ι),
      (U ∈ shearZFamilyM C_X C_Z σ hσ ∨ U ∈ shearXFamilyM C_X C_Z σ hσ) ∧
      (∀ b' : Finset ι, (∀ a ∈ b', σ a ∈ b') →
        IsTerminalLayer (localBlock b' (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) →
        localBlock b' ((U * G : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
            = localBlock b' (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∧
        localBlock b' ((G * U : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
            = localBlock b' (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ∧
      (localBlock b ((U * G : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = g' ∨
        localBlock b ((G * U : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = g') := by
  rcases hmove with ⟨ε, -, hside⟩ | ⟨ε, -, hside⟩
  · obtain ⟨U, hUfam, hUloc⟩ := exists_mem_shearZFamilyM_localBlock hσ hG ε
    refine ⟨U, Or.inl hUfam, fun b' hb' hterm' => ?_, ?_⟩
    · have hz : layerZParam (localBlock b' (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ε = 0 :=
        spzParam_eq_zero_of_isTerminalBlock hterm' ε
      exact ⟨by rw [(hUloc b' hb').1, hz, shearZ_zero, one_mul],
        by rw [(hUloc b' hb').2, hz, shearZ_zero, mul_one]⟩
    · exact hside.imp (fun h => by rw [(hUloc b hb).1, h]) fun h => by rw [(hUloc b hb).2, h]
  · obtain ⟨U, hUfam, hUloc⟩ := exists_mem_shearXFamilyM_localBlock hσ hG ε
    refine ⟨U, Or.inr hUfam, fun b' hb' hterm' => ?_, ?_⟩
    · have hx : layerXParam (localBlock b' (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ε = 0 :=
        spxParam_eq_zero_of_isTerminalBlock hterm' ε
      exact ⟨by rw [(hUloc b' hb').1, hx, shearX_zero, one_mul],
        by rw [(hUloc b' hb').2, hx, shearX_zero, mul_one]⟩
    · exact hside.imp (fun h => by rw [(hUloc b hb).1, h]) fun h => by rw [(hUloc b hb).2, h]

/-! ### Words in the two diagonal-circuit families -/

/-- A **word in the depth-one diagonal circuits on `M`**: a list of layers, each lying in `S^Z_M` or
in `S^X_M`. Its length is the number of multiplications performed — the quantity Lemma D.6 bounds by
`m₁ + 3 m₂`. -/
def IsShearWordM (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)) (σ : Equiv.Perm ι)
    (hσ : Function.Involutive σ) (L : List ↥(binarySymplecticGroup ι)) : Prop :=
  ∀ x ∈ L, x ∈ shearZFamilyM C_X C_Z σ hσ ∨ x ∈ shearXFamilyM C_X C_Z σ hσ

/-- The empty word (no multiplication at all) is a word in the two families. -/
theorem IsShearWordM.nil (hσ : Function.Involutive σ) : IsShearWordM C_X C_Z σ hσ [] :=
  List.forall_mem_nil _

/-- A one-letter word is a word in the two families exactly when its letter lies in one of them. -/
theorem IsShearWordM.singleton (hσ : Function.Involutive σ) {x : ↥(binarySymplecticGroup ι)} :
    IsShearWordM C_X C_Z σ hσ [x] ↔
      x ∈ shearZFamilyM C_X C_Z σ hσ ∨ x ∈ shearXFamilyM C_X C_Z σ hσ :=
  List.forall_mem_singleton

/-- A concatenation is a word in the two families exactly when both halves are. -/
theorem IsShearWordM.append (hσ : Function.Involutive σ)
    {L R : List ↥(binarySymplecticGroup ι)} :
    IsShearWordM C_X C_Z σ hσ (L ++ R) ↔
      IsShearWordM C_X C_Z σ hσ L ∧ IsShearWordM C_X C_Z σ hσ R :=
  List.forall_mem_append

/-- The product of a word lies in the subgroup generated by the two diagonal families. -/
theorem IsShearWordM.prod_mem_sup {hσ : Function.Involutive σ}
    {L : List ↥(binarySymplecticGroup ι)} (hL : IsShearWordM C_X C_Z σ hσ L) :
    L.prod ∈ shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ :=
  Subgroup.list_prod_mem _ fun x hx =>
    (hL x hx).elim Subgroup.mem_sup_left Subgroup.mem_sup_right

/-- The product of a word lies in the two-fold transversal slice `N_M` (both families do). -/
theorem IsShearWordM.prod_mem_slice {hσ : Function.Involutive σ}
    {L : List ↥(binarySymplecticGroup ι)} (hL : IsShearWordM C_X C_Z σ hσ L) :
    L.prod ∈ fixedMatchingSlice C_X C_Z σ hσ :=
  sup_le (shearZFamilyM_le_fixedMatchingSlice C_X C_Z σ hσ)
    (shearXFamilyM_le_fixedMatchingSlice C_X C_Z σ hσ) hL.prod_mem_sup

/-! ### One phase: driving a single cell to a terminal block -/

/-- **One phase of the reduction (the inner induction of Lemma D.6).** Suppose the cell block `g_𝔟`
of `G ∈ N_M` reaches a terminal block in at most `k` local moves — which is what Lemma D.4 supplies.
Then `G` can be carried, by **at most `k`** left and right multiplications with elements of
`S^Z_M ∪ S^X_M`, to a layer whose block at `𝔟` is terminal, **without undoing any cell that was
already terminal**.

The induction is on `k`, one letter being appended to the left or the right word per move — which is
what makes the multiplication count come out as the local move count. Each move is realized by a
single global generator (`exists_mem_shearFamilyM_of_isBlockMove`, which also supplies the
freezing of the already-terminal cells), so only the side of the multiplication is left to
distinguish. The other cells "may move arbitrarily" — except the terminal ones, which are
untouched. -/
theorem exists_reduce_cell (hσ : Function.Involutive σ) {k : ℕ} {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b)
    {G : ↥(binarySymplecticGroup ι)} (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ)
    (hreach : ReachesTerminalIn k (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))) :
    ∃ L R : List ↥(binarySymplecticGroup ι),
      IsShearWordM C_X C_Z σ hσ L ∧ IsShearWordM C_X C_Z σ hσ R ∧
      L.length + R.length ≤ k ∧
      IsTerminalLayer (localBlock b
        ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) ∧
      ∀ b' : Finset ι, (∀ a ∈ b', σ a ∈ b') →
        IsTerminalLayer (localBlock b' (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) →
        IsTerminalLayer (localBlock b'
          ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
            Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) := by
  induction k generalizing G with
  | zero =>
    exact ⟨[], [], .nil hσ, .nil hσ, by simp, by simpa using hreach,
      fun b' _ h => by simpa using h⟩
  | succ k ih =>
    rcases hreach with hterm | ⟨g', hmove, hreach'⟩
    · exact ⟨[], [], .nil hσ, .nil hσ, by simp, by simpa using hterm,
        fun b' _ h => by simpa using h⟩
    obtain ⟨U, hUfam, hfreeze, hside⟩ := exists_mem_shearFamilyM_of_isBlockMove hσ hb hG hmove
    have hUN : U ∈ fixedMatchingSlice C_X C_Z σ hσ :=
      hUfam.elim (fun h => shearZFamilyM_le_fixedMatchingSlice C_X C_Z σ hσ h)
        fun h => shearXFamilyM_le_fixedMatchingSlice C_X C_Z σ hσ h
    rcases hside with hloc | hloc
    · -- left multiplication: the new letter is appended on the left word
      obtain ⟨L, R, hL, hR, hlen, hterm₁, hpres₁⟩ :=
        ih (mul_mem hUN hG) (by rw [hloc]; exact hreach')
      have hassoc : (L ++ [U]).prod * G * R.prod = L.prod * (U * G) * R.prod := by
        rw [List.prod_append, List.prod_singleton, mul_assoc L.prod U G]
      refine ⟨L ++ [U], R, (IsShearWordM.append hσ).mpr
          ⟨hL, (IsShearWordM.singleton hσ).mpr hUfam⟩, hR, ?_, ?_, fun b' hb' h' => ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · rw [hassoc]; exact hterm₁
      · rw [hassoc]
        exact hpres₁ b' hb' (by rw [(hfreeze b' hb' h').1]; exact h')
    · -- right multiplication: the new letter is prepended to the right word
      obtain ⟨L, R, hL, hR, hlen, hterm₁, hpres₁⟩ :=
        ih (mul_mem hG hUN) (by rw [hloc]; exact hreach')
      have hassoc : L.prod * G * ([U] ++ R).prod = L.prod * (G * U) * R.prod := by
        rw [List.prod_append, List.prod_singleton]; group
      refine ⟨L, [U] ++ R, hL, (IsShearWordM.append hσ).mpr
          ⟨(IsShearWordM.singleton hσ).mpr hUfam, hR⟩, ?_, ?_, fun b' hb' h' => ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · rw [hassoc]; exact hterm₁
      · rw [hassoc]
        exact hpres₁ b' hb' (by rw [(hfreeze b' hb' h').2]; exact h')

/-! ### The cells of the matching, their widths, and the move budget `m₁ + 3 m₂` -/

/-- **The cells of the matching `M`**, as a finset: the images `{i, σ i}` of the qubits
(`cellFinset σ`). The outer induction of Lemma D.6 runs on them. -/
def matchingCells (σ : Equiv.Perm ι) : Finset (Finset ι) := Finset.univ.image (cellFinset σ)

/-- Membership in `matchingCells`: the cells are exactly the sets `{i, σ i}`. -/
@[simp] theorem mem_matchingCells {b : Finset ι} :
    b ∈ matchingCells σ ↔ ∃ i, cellFinset σ i = b := by
  simp [matchingCells]

/-- Every qubit's cell is a cell of the matching. -/
theorem cellFinset_mem_matchingCells (σ : Equiv.Perm ι) (i : ι) :
    cellFinset σ i ∈ matchingCells σ :=
  mem_matchingCells.mpr ⟨i, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The **move budget of a cell**: `1` for a cell of width one, `3` for a cell of width two — the
per-block bounds of Lemma D.4. Summed over the cells this is the paper's `m₁ + 3 m₂`. -/
def cellMoveBound (b : Finset ι) : ℕ := if b.card ≤ 1 then 1 else 3

omit [Fintype ι] [DecidableEq ι] in
/-- A width-one cell has budget `1`. -/
theorem cellMoveBound_of_card_eq_one {b : Finset ι} (hb : b.card = 1) : cellMoveBound b = 1 := by
  rw [cellMoveBound, if_pos hb.le]

omit [Fintype ι] [DecidableEq ι] in
/-- A width-two cell has budget `3`. -/
theorem cellMoveBound_of_card_eq_two {b : Finset ι} (hb : b.card = 2) : cellMoveBound b = 3 := by
  rw [cellMoveBound, if_neg (by omega)]

/-- The **width-one cells** (the unmatched qubits, each a singleton cell); their number is the
paper's `m₁`. -/
def singletonCells (σ : Equiv.Perm ι) : Finset (Finset ι) :=
  (matchingCells σ).filter fun b => b.card = 1

/-- The **width-two cells** (the matched pairs); their number is the paper's `m₂`. -/
def pairCells (σ : Equiv.Perm ι) : Finset (Finset ι) :=
  (matchingCells σ).filter fun b => b.card = 2

/-- Every cell is closed under the matching (`{i, σ i}` is `σ`-stable), the hypothesis under which
restriction to it is multiplicative. -/
theorem sigma_closed_of_mem_matchingCells (hσ : Function.Involutive σ) {b : Finset ι}
    (hb : b ∈ matchingCells σ) : ∀ a ∈ b, σ a ∈ b := by
  obtain ⟨i, rfl⟩ := mem_matchingCells.mp hb
  exact cellFinset_sigma_closed hσ i

omit [Fintype ι] in
/-- **A cell has width one or two**: `#{i, σ i} = 1` if the qubit `i` is unmatched (`σ i = i`) and
`2` if it is matched. This is two-locality: "the cells partition the qubits into blocks of size one
or two". -/
theorem card_cellFinset (σ : Equiv.Perm ι) (i : ι) :
    (cellFinset σ i).card = if σ i = i then 1 else 2 := by
  rcases eq_or_ne (σ i) i with h | h
  · rw [if_pos h, cellFinset, h]
    simp
  · rw [if_neg h, cellFinset]
    exact Finset.card_pair (Ne.symm h)

/-- Every cell has width one or two (`card_cellFinset`, forgetting which). -/
theorem card_eq_one_or_two_of_mem_matchingCells {b : Finset ι} (hb : b ∈ matchingCells σ) :
    b.card = 1 ∨ b.card = 2 := by
  obtain ⟨i, rfl⟩ := mem_matchingCells.mp hb
  rw [card_cellFinset]
  split <;> simp

/-- **The total move budget is the paper's `m₁ + 3 m₂`.** Every cell has width one or two, so the
cells split into the `m₁` singleton cells, each contributing `1`, and the `m₂` pair cells, each
contributing `3`. -/
theorem sum_cellMoveBound (σ : Equiv.Perm ι) :
    ∑ b ∈ matchingCells σ, cellMoveBound b
      = (singletonCells σ).card + 3 * (pairCells σ).card := by
  have hone : ∑ b ∈ (matchingCells σ).filter (fun b => b.card = 1), cellMoveBound b
      = ((matchingCells σ).filter (fun b => b.card = 1)).card * 1 :=
    Finset.sum_const_nat fun b hb => cellMoveBound_of_card_eq_one (Finset.mem_filter.mp hb).2
  have hnot : (matchingCells σ).filter (fun b => ¬ b.card = 1)
      = (matchingCells σ).filter fun b => b.card = 2 := by
    refine Finset.filter_congr fun b hb => ?_
    rcases card_eq_one_or_two_of_mem_matchingCells hb with h | h <;> simp [h]
  have htwo : ∑ b ∈ (matchingCells σ).filter (fun b => ¬ b.card = 1), cellMoveBound b
      = ((matchingCells σ).filter (fun b => ¬ b.card = 1)).card * 3 :=
    Finset.sum_const_nat fun b hb => by
      obtain ⟨hbm, hb1⟩ := Finset.mem_filter.mp hb
      exact cellMoveBound_of_card_eq_two
        ((card_eq_one_or_two_of_mem_matchingCells hbm).resolve_left hb1)
  rw [← Finset.sum_filter_add_sum_filter_not (matchingCells σ) (fun b => b.card = 1) cellMoveBound,
    hone, htwo, hnot, singletonCells, pairCells]
  ring

/-- **Lemma D.4 applied to a cell of the layer.** A cell has width one or two, its block is
symplectic (`localBlock_mem_binarySymplecticGroup`), so the local reduction — the proved width-one
half `localReduction_width_one` for an unmatched qubit, the assumed width-two half for a matched
pair — carries that block to a terminal one within the cell's move budget. -/
theorem reachesTerminalIn_cellMoveBound (hD4 : LocalReduction.{u} 2 3)
    (hσ : Function.Involutive σ) (i : ι) {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) :
    ReachesTerminalIn (cellMoveBound (cellFinset σ i))
      (localBlock (cellFinset σ i) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) := by
  have hsymp : localBlock (cellFinset σ i) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      ∈ binarySymplecticGroup (cellFinset σ i) :=
    localBlock_mem_binarySymplecticGroup (cellFinset_sigma_closed hσ i) G.2
      (mem_fixedMatchingSlice_iff.mp hG).2
  rcases eq_or_ne (σ i) i with h | h
  · have hc : (cellFinset σ i).card = 1 := by rw [card_cellFinset, if_pos h]
    rw [cellMoveBound_of_card_eq_one hc]
    exact localReduction_width_one _ (by rw [Fintype.card_coe, hc]) _ hsymp
  · have hc : (cellFinset σ i).card = 2 := by rw [card_cellFinset, if_neg h]
    rw [cellMoveBound_of_card_eq_two hc]
    exact hD4 _ (by rw [Fintype.card_coe, hc]) _ hsymp

/-! ### Lemma D.6 (Global reduction) -/

/-- **The cell-by-cell induction of Lemma D.6.** If every cell in `T` is already terminal for
`G ∈ N_M`, then `G` can be carried to a layer *all* of whose cells are terminal, by a word of
diagonal circuits on each side whose total length is at most the move budget
`∑_{𝔟 ∉ T} cellMoveBound 𝔟` of the unfinished cells.

The recursion is on the number `#(cells \ T)` of unfinished cells: one phase
(`exists_reduce_cell`) finishes one further cell within its own budget and without disturbing the
cells of `T`, so the set of unfinished cells strictly shrinks — "terminality is absorbing", and no
control at all is needed over the cells that are neither finished nor being processed. -/
theorem exists_terminal_cells (hD4 : LocalReduction.{u} 2 3) (hσ : Function.Involutive σ)
    {T : Finset (Finset ι)} {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) (hT : T ⊆ matchingCells σ)
    (hterm : ∀ b ∈ T, IsTerminalLayer (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))) :
    ∃ L R : List ↥(binarySymplecticGroup ι),
      IsShearWordM C_X C_Z σ hσ L ∧ IsShearWordM C_X C_Z σ hσ R ∧
      L.length + R.length ≤ ∑ b ∈ matchingCells σ \ T, cellMoveBound b ∧
      ∀ b ∈ matchingCells σ, IsTerminalLayer (localBlock b
        ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) := by
  -- the recursion measure `#(cells \ T)` is bounded inside the proof; it is not part of the
  -- statement
  suffices H : ∀ (m : ℕ) (T : Finset (Finset ι)) (G : ↥(binarySymplecticGroup ι)),
      (matchingCells σ \ T).card ≤ m → G ∈ fixedMatchingSlice C_X C_Z σ hσ →
      T ⊆ matchingCells σ →
      (∀ b ∈ T, IsTerminalLayer (localBlock b (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))) →
      ∃ L R : List ↥(binarySymplecticGroup ι),
        IsShearWordM C_X C_Z σ hσ L ∧ IsShearWordM C_X C_Z σ hσ R ∧
        L.length + R.length ≤ ∑ b ∈ matchingCells σ \ T, cellMoveBound b ∧
        ∀ b ∈ matchingCells σ, IsTerminalLayer (localBlock b
          ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
            Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) by
    exact H _ T G le_rfl hG hT hterm
  intro m
  induction m with
  | zero =>
    intro T G hcard hG hT hterm
    have hsub : matchingCells σ ⊆ T :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
    exact ⟨[], [], .nil hσ, .nil hσ, by simp,
      fun b hb => by simpa using hterm b (hsub hb)⟩
  | succ m ih =>
    intro T G hcard hG hT hterm
    by_cases hsub : matchingCells σ ⊆ T
    · exact ⟨[], [], .nil hσ, .nil hσ, by simp,
        fun b hb => by simpa using hterm b (hsub hb)⟩
    obtain ⟨b, hbcells, hbT⟩ := Finset.not_subset.mp hsub
    obtain ⟨i, rfl⟩ := mem_matchingCells.mp hbcells
    obtain ⟨L₁, R₁, hL₁, hR₁, hlen₁, hterm₁, hpres₁⟩ :=
      exists_reduce_cell hσ (cellFinset_sigma_closed hσ i) hG
        (reachesTerminalIn_cellMoveBound hD4 hσ i hG)
    have hG₁ : L₁.prod * G * R₁.prod ∈ fixedMatchingSlice C_X C_Z σ hσ :=
      mul_mem (mul_mem hL₁.prod_mem_slice hG) hR₁.prod_mem_slice
    have hmemsdiff : cellFinset σ i ∈ matchingCells σ \ T := Finset.mem_sdiff.mpr ⟨hbcells, hbT⟩
    have hcard' : (matchingCells σ \ insert (cellFinset σ i) T).card ≤ m := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hmemsdiff]
      have hpos : 1 ≤ (matchingCells σ \ T).card := Finset.card_pos.mpr ⟨_, hmemsdiff⟩
      omega
    obtain ⟨L₂, R₂, hL₂, hR₂, hlen₂, hcells⟩ :=
      ih (insert (cellFinset σ i) T) (L₁.prod * G * R₁.prod) hcard' hG₁
        (Finset.insert_subset hbcells hT)
        (by
          intro b' hb'
          rcases Finset.mem_insert.mp hb' with rfl | hb'
          · exact hterm₁
          · exact hpres₁ b' (sigma_closed_of_mem_matchingCells hσ (hT hb')) (hterm b' hb'))
    have hbudget : ∑ b ∈ matchingCells σ \ insert (cellFinset σ i) T, cellMoveBound b
        + cellMoveBound (cellFinset σ i) = ∑ b ∈ matchingCells σ \ T, cellMoveBound b := by
      rw [Finset.sdiff_insert, add_comm]
      exact Finset.add_sum_erase _ _ hmemsdiff
    have hassoc : (L₂ ++ L₁).prod * G * (R₁ ++ R₂).prod
        = L₂.prod * (L₁.prod * G * R₁.prod) * R₂.prod := by
      rw [List.prod_append, List.prod_append]; group
    refine ⟨L₂ ++ L₁, R₁ ++ R₂, (IsShearWordM.append hσ).mpr ⟨hL₂, hL₁⟩,
      (IsShearWordM.append hσ).mpr ⟨hR₁, hR₂⟩, ?_, fun b hb => ?_⟩
    · simp only [List.length_append]
      omega
    · rw [hassoc]
      exact hcells b hb

/-- **Lemma D.6 (Global reduction), conditional on Lemma D.4.** Every `G ∈ N_M` can be carried to a
layer `G_term ∈ N_M` all of whose cell blocks are terminal, by left and right multiplication with
elements of `S^Z_M` and `S^X_M`; **at most `m₁ + 3 m₂` such multiplications are required**, `m₁` and
`m₂` being the numbers of cells of width one and two (`singletonCells`, `pairCells`). The two
multiplication words are returned explicitly as lists `L`, `R` of family elements, so their total
length *is* the number of multiplications performed.

Terminality is delivered in both of the paper's readings: blockwise ("all of whose cell blocks are
terminal") and, equivalently for an `M`-block-diagonal layer, as terminality of the layer itself
(`isTerminalLayer_of_forall_cell`), the form the terminal factorization consumes.

The hypothesis is the width-two half of Lemma D.4; its width-one half is `localReduction_width_one`,
proved. -/
theorem exists_terminalLayer_of_localReduction (hD4 : LocalReduction.{u} 2 3)
    (hσ : Function.Involutive σ) {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) :
    ∃ L R : List ↥(binarySymplecticGroup ι),
      IsShearWordM C_X C_Z σ hσ L ∧ IsShearWordM C_X C_Z σ hσ R ∧
      L.length + R.length ≤ (singletonCells σ).card + 3 * (pairCells σ).card ∧
      L.prod * G * R.prod ∈ fixedMatchingSlice C_X C_Z σ hσ ∧
      (∀ b ∈ matchingCells σ, IsTerminalLayer (localBlock b
        ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))) ∧
      IsTerminalLayer
        ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) := by
  obtain ⟨L, R, hL, hR, hlen, hcells⟩ :=
    exists_terminal_cells hD4 hσ hG (Finset.empty_subset _) (by simp)
  have hGterm : L.prod * G * R.prod ∈ fixedMatchingSlice C_X C_Z σ hσ :=
    mul_mem (mul_mem hL.prod_mem_slice hG) hR.prod_mem_slice
  refine ⟨L, R, hL, hR, ?_, hGterm, hcells, ?_⟩
  · rw [← sum_cellMoveBound σ]
    simpa using hlen
  · exact isTerminalLayer_of_forall_cell hσ (mem_fixedMatchingSlice_iff.mp hGterm).2
      fun i => hcells _ (cellFinset_mem_matchingCells σ i)

/-! ### Theorem D.1, conditional on Lemma D.4 -/

/-- **Theorem D.1 (Fixed-matching generation), CONDITIONAL on Lemma D.4.** For every CSS-form label
space and every matching `M`,
`N_M = ⟨S^Z_M, S^X_M, L_M⟩ = S^Z_M ⊔ S^X_M ⊔ L_M` — *assuming* the width-two half
`LocalReduction 2 3` of **Lemma D.4 (Local reduction)**, which the paper establishes by exhaustive
computer verification of the `720` elements of `Sp(4, 𝔽₂)` and which is **not formalized here**. The
width-one half
of Lemma D.4 is proved (`localReduction_width_one`, `terminalBlocks_width_one`), so this hypothesis
is strictly weaker than the paper's lemma. *This theorem is therefore not Theorem D.1 itself but the
implication "Lemma D.4 ⟹ Theorem D.1".*

`⊇` is the easy inclusion `sup_familyM_le_fixedMatchingSlice`. For `⊆`, Lemma D.6
(`exists_terminalLayer_of_localReduction`) produces words `L`, `R` in `S^Z_M ∪ S^X_M` with
`L.prod · G · R.prod` terminal; the terminal factorization (`terminalLayer_mem_sup_familyM`,
Eq. (d1-factor)) puts that layer in the join; and `G = L.prod⁻¹ (L.prod G R.prod) R.prod⁻¹` then
exhibits `G` as a group word in the three families. -/
theorem fixedMatchingSlice_eq_sup_familyM_of_localReduction (hD4 : LocalReduction.{u} 2 3)
    (hσ : Function.Involutive σ) :
    fixedMatchingSlice C_X C_Z σ hσ
      = shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ ⊔ leviFamilyM C_X C_Z σ hσ := by
  refine le_antisymm (fun G hG => ?_) (sup_familyM_le_fixedMatchingSlice C_X C_Z σ hσ)
  obtain ⟨L, R, hL, hR, -, hGterm, -, hterm⟩ := exists_terminalLayer_of_localReduction hD4 hσ hG
  have hmem : L.prod * G * R.prod ∈ shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ
      ⊔ leviFamilyM C_X C_Z σ hσ :=
    terminalLayer_mem_sup_familyM hσ (Matrix.fromBlocks_toBlocks _).symm hGterm hterm
  have hGeq : G = L.prod⁻¹ * (L.prod * G * R.prod) * R.prod⁻¹ := by group
  rw [hGeq]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hL.prod_mem_sup)) hmem)
    (Subgroup.mem_sup_left (inv_mem hR.prod_mem_sup))

end CliffordCSS
