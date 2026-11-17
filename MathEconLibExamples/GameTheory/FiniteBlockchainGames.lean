/-
Copyright (c) 2026 Yaron Velner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaron Velner
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import MathEconLib.Probability.FinDist.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite blockchain games

Concrete finite blockchain games formalized as strategic games.

Blocks store **child indices** into `Blockchain.blocks`, so updates to a parent in
the flat block list are visible to every traversal (including payoff). Index `0`
is always the genesis block.

## Main definitions

* `Miner`, `Block`, `Blockchain`: Miners and the block-tree representation.
* `Blockchain.initial`: Genesis-only chain.
* `MinerStrategy`, `MinerStrategyProfile`: Parent-index choice; one strategy per miner.
* `step`, `execution`: One mining round; finite-horizon play under lottery draws.
* `winCount`: How often a miner is selected in a sequence of lottery draws.
* `Blockchain.minerCount`: How many blocks in the chain were mined by a given miner.
* `Blockchain.payoff`: Longest-chain length, witnessing child index, and miner payoff.
* `strategySequencePayoff`: Miner payoff after `k` moves under a profile and draws.
* `Blockchain.WellFormed`: Child indices point forward into the block array.
* `payoff_le_minerCount`, `strategySequencePayoff_le_winCount`: Payoff bounds.

## Tags

blockchain games, strategic games, nash equilibrium
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibExamples.GameTheory.FiniteBlockchainGames


variable {n : Nat}

abbrev Miner (n : Nat) := Fin n

/-- A block with its miner and the indices of its child blocks in `Blockchain.blocks`. -/
structure Block (n : Nat) where
  miner : Option (Miner n)
  children : List Nat
  deriving Repr

/-- A blockchain as a flat block list; genesis is `blocks[0]`. -/
structure Blockchain (n : Nat) where
  blocks : List (Block n)
  deriving Repr

/-- Initialize a blockchain containing only genesis. -/
def Blockchain.initial (n : Nat) : Blockchain n :=
  { blocks := [{ miner := none, children := [] }] }

abbrev Bitcoin :=
  Blockchain.initial n

/-- A miner strategy chooses a parent block index from the current chain. -/
abbrev MinerStrategy (n : Nat) := (b : Blockchain n) → Fin b.blocks.length

/-- A strategy for each miner. -/
abbrev MinerStrategyProfile (n : Nat) := Miner n → MinerStrategy n

/-- Apply miner `miner`'s strategy on `b` and insert the resulting block. -/
def step (σ : MinerStrategyProfile n) (b : Blockchain n) (miner : Miner n) :
    Blockchain n :=
  let parentIdx := σ miner b
  let parent := b.blocks[parentIdx]
  let newIdx := b.blocks.length
  let newNode : Block n := { miner := some miner, children := [] }
  let parent' : Block n := { parent with children := parent.children ++ [newIdx] }
  { blocks := b.blocks.set parentIdx.val parent' ++ [newNode] }

/-- Finite execution of length `k`. At each step the fair lottery supplies the
winning miner in `draws`; that miner attaches a block to the parent chosen by
its strategy on the chain produced so far. Length `0` returns `Bitcoin`. -/
def execution (σ : MinerStrategyProfile n) :
    (k : Nat) → (draws : Fin k → Miner n) → Blockchain n
  | 0, _ => Bitcoin
  | k + 1, draws =>
      step σ (execution σ k (fun i ↦ draws i.castSucc)) (draws (Fin.last k))

/-- Number of times miner `m` is selected in the lottery draw sequence. -/
def winCount {k : Nat} (draws : Fin k → Miner n) (m : Miner n) : Nat :=
  (Finset.univ.filter (fun i : Fin k ↦ draws i = m)).card

/-- Boolean test that a block was mined by `m`. -/
def minedBy (m : Miner n) (block : Block n) : Bool :=
  decide (block.miner = some m)

/-- Number of blocks in `b` mined by `m`. -/
def Blockchain.minerCount (b : Blockchain n) (m : Miner n) : Nat :=
  b.blocks.countP (minedBy m)

/-- Among annotated child indices, choose the earliest with maximal length. -/
def earliestLongest : List (Nat × Nat × Nat) → Option (Nat × Nat × Nat)
  | [] => none
  | (c, cl, cp) :: cs =>
      match earliestLongest cs with
      | none => some (c, cl, cp)
      | some (c', cl', cp') =>
          if cl < cl' then some (c', cl', cp') else some (c, cl, cp)

/-- Longest-chain data from node `idx` for miner `m`: chain length (inclusive), a
child index realising that length (if any; earliest on ties), and `m`'s payoff
along that path. -/
def Blockchain.payoff (b : Blockchain n) (m : Miner n) (idx : Nat) :
    Nat × Option Nat × Nat :=
  payoffAux b.blocks.length idx
where
  payoffAux : Nat → Nat → Nat × Option Nat × Nat
  | 0, _ => (1, none, 0)
  | fuel + 1, idx =>
      match b.blocks[idx]? with
      | none => (1, none, 0)
      | some block =>
          let own : Nat := if block.miner = some m then 1 else 0
          let annotated : List (Nat × Nat × Nat) :=
            block.children.map fun cidx =>
              let (cl, _, cp) := payoffAux fuel cidx
              (cidx, cl, cp)
          match earliestLongest annotated with
          | none => (1, none, own)
          | some (cidx, cl, cp) => (1 + cl, some cidx, own + cp)

/-- Payoff of miner `m` after `k` moves under strategy profile `σ` and lottery
draw sequence `draws`, evaluated from genesis of the resulting chain. -/
def strategySequencePayoff (σ : MinerStrategyProfile n) (k : Nat)
    (draws : Fin k → Miner n) (m : Miner n) : Nat :=
  ((execution σ k draws).payoff m 0).2.2

/-!
## Relating block counts to lottery wins
-/

/-- One mining step adds a block of `miner` and does not retarget existing miners. -/
lemma minerCount_step (σ : MinerStrategyProfile n) (b : Blockchain n)
    (miner m : Miner n) :
    (step σ b miner).minerCount m =
      b.minerCount m + if miner = m then 1 else 0 := by
  dsimp [Blockchain.minerCount, step]
  set i := σ miner b
  set parent := b.blocks[i]
  set parent' : Block n := { parent with children := parent.children ++ [b.blocks.length] }
  set newNode : Block n := { miner := some miner, children := [] }
  have hi : i.val < b.blocks.length := i.is_lt
  change (b.blocks.set i.val parent' ++ [newNode]).countP (minedBy m) =
    b.blocks.countP (minedBy m) + if miner = m then 1 else 0
  have hget : b.blocks[i.val] = parent := by simp [i, parent]
  have hminer : minedBy m parent' = minedBy m parent := by simp [minedBy, parent']
  have hle : (if minedBy m parent then 1 else 0) ≤ b.blocks.countP (minedBy m) := by
    simpa [hget] using List.boole_getElem_le_countP (p := minedBy m) hi
  have hnew : [newNode].countP (minedBy m) = if miner = m then 1 else 0 := by
    simp [minedBy, newNode, List.countP_cons, List.countP_nil]
  rw [List.countP_append, List.countP_set hi, hget, hminer, hnew, Nat.sub_add_cancel hle]

/-- `winCount` equals the sum of win indicators. -/
lemma winCount_eq_sum {k : Nat} (draws : Fin k → Miner n) (m : Miner n) :
    winCount draws m = ∑ i : Fin k, if draws i = m then 1 else 0 := by
  classical
  simp [winCount, Finset.sum_boole]

/-- Extending the draw sequence by one step updates `winCount` by a 0/1 indicator. -/
lemma winCount_succ {k : Nat} (draws : Fin (k + 1) → Miner n) (m : Miner n) :
    winCount draws m =
      winCount (fun i : Fin k ↦ draws i.castSucc) m +
        if draws (Fin.last k) = m then 1 else 0 := by
  simp only [winCount_eq_sum, Fin.sum_univ_castSucc]

/-- After any finite execution, miner `m`'s blocks are exactly their lottery wins. -/
theorem minerCount_le_winCount (σ : MinerStrategyProfile n) (k : Nat)
    (draws : Fin k → Miner n) (m : Miner n) :
    (execution σ k draws).minerCount m ≤ winCount draws m := by
  have hEq : (execution σ k draws).minerCount m = winCount draws m := by
    induction k with
    | zero =>
        simp [execution, Bitcoin, Blockchain.initial, Blockchain.minerCount, winCount,
          minedBy]
    | succ k ih =>
        rw [execution, minerCount_step, winCount_succ, ih]
  exact hEq.le

/-!
## Well-formed trees and payoff paths

Every child index produced by `step` is a freshly appended node, so edges always
go to a strictly larger index. Along any child path, indices are therefore
strictly increasing and in particular pairwise distinct.
-/

/-- A chain is well-formed when it is nonempty and every child index is a valid
node strictly after its parent. -/
def Blockchain.WellFormed (b : Blockchain n) : Prop :=
  b.blocks ≠ [] ∧
    ∀ (i c : Nat) (hi : i < b.blocks.length),
      c ∈ b.blocks[i].children → i < c ∧ c < b.blocks.length

lemma wellFormed_initial : (Blockchain.initial n).WellFormed := by
  refine ⟨by simp [Blockchain.initial], ?_⟩
  intro i c hi hc
  have hi0 : i = 0 := by
    simp only [Blockchain.initial, List.length_cons, List.length_nil] at hi
    omega
  subst hi0
  simp only [Blockchain.initial, List.getElem_cons_zero] at hc
  cases hc

lemma wellFormed_bitcoin : (Bitcoin : Blockchain n).WellFormed :=
  wellFormed_initial

/-- Values returned by `earliestLongest` are members of its input list. -/
lemma earliestLongest_mem :
    ∀ (l : List (Nat × Nat × Nat)) {c cl cp : Nat},
      earliestLongest l = some (c, cl, cp) → (c, cl, cp) ∈ l
  | [], _, _, _, h => by simp [earliestLongest] at h
  | (c₀, cl₀, cp₀) :: cs, c, cl, cp, h => by
      simp only [earliestLongest] at h
      cases hcs : earliestLongest cs with
      | none =>
          simp only [hcs, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact List.mem_cons_self
      | some p =>
          simp only [hcs] at h
          split_ifs at h with _hlt
          · obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
            exact List.mem_cons_of_mem _ (earliestLongest_mem cs hcs)
          · obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
            exact List.mem_cons_self

/-- `step` preserves well-formedness. -/
lemma wellFormed_step (σ : MinerStrategyProfile n) (b : Blockchain n) (miner : Miner n)
    (hw : b.WellFormed) : (step σ b miner).WellFormed := by
  obtain ⟨hne, hch⟩ := hw
  refine ⟨by simp [step], ?_⟩
  intro i c hi hc
  -- Goal length first, so we never rewrite a Fin-dependent length.
  suffices hmain : i < c ∧ c < b.blocks.length + 1 by
    simpa [step] using hmain
  have hi_step : i < (step σ b miner).blocks.length := hi
  let parentIdx := σ miner b
  let parent := b.blocks[parentIdx]
  let newIdx := b.blocks.length
  let parent' : Block n := { parent with children := parent.children ++ [newIdx] }
  let newNode : Block n := { miner := some miner, children := [] }
  let blocks' := b.blocks.set parentIdx.val parent' ++ [newNode]
  have hblocks : (step σ b miner).blocks = blocks' := rfl
  have hlen : blocks'.length = newIdx + 1 := by simp [blocks', newIdx, parent', newNode]
  have hi' : i < blocks'.length := by simpa [hblocks] using hi_step
  have hc' : c ∈ (blocks'[i]'hi').children := by
    have hget : (step σ b miner).blocks[i]'hi_step = blocks'[i]'hi' := by
      simp [hblocks]
    exact (congrArg Block.children hget) ▸ hc
  by_cases hlt : i < newIdx
  · have hi_set : i < (b.blocks.set parentIdx.val parent').length := by
      simpa [List.length_set, newIdx] using hlt
    have hleft := List.getElem_append_left (as := b.blocks.set parentIdx.val parent')
      (bs := [newNode]) (h := hi_set) (h' := hi')
    have hc_set : c ∈ ((b.blocks.set parentIdx.val parent')[i]'hi_set).children := by
      have : blocks'[i]'hi' = (b.blocks.set parentIdx.val parent')[i]'hi_set := by
        simpa [blocks'] using hleft
      exact (congrArg Block.children this) ▸ hc'
    by_cases hEq : i = parentIdx.val
    · have hset : (b.blocks.set parentIdx.val parent')[i]'hi_set = parent' := by
        simp [hEq]
      have hc'' : c ∈ parent'.children := (congrArg Block.children hset) ▸ hc_set
      simp only [parent', List.mem_append, List.mem_singleton] at hc''
      rcases hc'' with hc'' | rfl
      · have ⟨h₁, h₂⟩ :=
          hch parentIdx.val c (by simp)
            (by simpa [parent, parentIdx] using hc'')
        exact ⟨hEq ▸ h₁, Nat.lt_succ_of_lt (by simpa [newIdx] using h₂)⟩
      · exact ⟨hEq ▸ parentIdx.is_lt, by omega⟩
    · have hset : (b.blocks.set parentIdx.val parent')[i]'hi_set = b.blocks[i] :=
        List.getElem_set_ne (l := b.blocks) (i := parentIdx.val) (j := i) (Ne.symm hEq)
          (hj := by simpa [newIdx] using hlt)
      have hc'' : c ∈ b.blocks[i].children := (congrArg Block.children hset) ▸ hc_set
      have ⟨h₁, h₂⟩ := hch i c (by simpa [newIdx] using hlt) hc''
      exact ⟨h₁, Nat.lt_succ_of_lt (by simpa [newIdx] using h₂)⟩
  · have hi_eq : i = newIdx := by omega
    have hge : (b.blocks.set parentIdx.val parent').length ≤ i := by
      simp [hi_eq, List.length_set, newIdx]
    have hright := List.getElem_append_right (as := b.blocks.set parentIdx.val parent')
      (bs := [newNode]) hge (h₂ := hi')
    have hget : blocks'[i]'hi' = newNode := by
      rw [show blocks'[i]'hi' = (b.blocks.set parentIdx.val parent' ++ [newNode])[i]'hi' from rfl,
        hright]
      simp [hi_eq, List.length_set, newIdx]
    have hc'' : c ∈ newNode.children := (congrArg Block.children hget) ▸ hc'
    simp [newNode] at hc''

lemma wellFormed_execution (σ : MinerStrategyProfile n) (k : Nat)
    (draws : Fin k → Miner n) : (execution σ k draws).WellFormed := by
  induction k with
  | zero => simpa [execution] using wellFormed_bitcoin
  | succ k ih =>
      exact wellFormed_step σ _ _ (ih _)

/-- The witnessing child chosen by `payoff`, if any. -/
def Blockchain.payoffChild (b : Blockchain n) (m : Miner n) (idx : Nat) : Option Nat :=
  (b.payoff m idx).2.1

/-- If `payoffAux (fuel+1)` returns a child, that child is in the node's `children`. -/
lemma mem_children_of_payoffAux_succ (b : Blockchain n) (m : Miner n)
    (fuel idx c : Nat) (hidx : idx < b.blocks.length)
    (hc : (Blockchain.payoff.payoffAux b m (fuel + 1) idx).2.1 = some c) :
    c ∈ b.blocks[idx].children := by
  simp only [Blockchain.payoff.payoffAux, List.getElem?_eq_getElem hidx] at hc
  split at hc
  · cases hc
  · next cidx cl cp hel =>
      simp only [Option.some.injEq] at hc
      subst hc
      have hmem := earliestLongest_mem _ hel
      obtain ⟨c', hc', heq⟩ := List.mem_map.mp hmem
      have : c' = cidx := congrArg Prod.fst heq
      exact this ▸ hc'

/-- On a well-formed chain, a `payoff` child is an in-range child of `idx`. -/
lemma mem_children_of_payoffChild {b : Blockchain n} (hw : b.WellFormed)
    (m : Miner n) {idx c : Nat} (hc : b.payoffChild m idx = some c)
    (hidx : idx < b.blocks.length) :
    c ∈ b.blocks[idx].children ∧ idx < c ∧ c < b.blocks.length := by
  obtain ⟨_, hch⟩ := hw
  unfold Blockchain.payoffChild Blockchain.payoff at hc
  have hfuel : ∃ fuel, b.blocks.length = fuel + 1 := ⟨b.blocks.length - 1, by omega⟩
  obtain ⟨fuel, hf⟩ := hfuel
  rw [hf] at hc
  have hmem := mem_children_of_payoffAux_succ b m fuel idx c hidx hc
  have ⟨h₁, h₂⟩ := hch idx c hidx hmem
  exact ⟨hmem, h₁, h₂⟩

/-- Indices visited while computing `payoff` from `idx` (including `idx`). -/
def Blockchain.payoffPath (b : Blockchain n) (m : Miner n) (idx : Nat) : List Nat :=
  pathAux b.blocks.length idx
where
  pathAux : Nat → Nat → List Nat
  | 0, idx => [idx]
  | fuel + 1, idx =>
      idx ::
        match b.payoffChild m idx with
        | none => []
        | some c => pathAux fuel c

/-- Strict increase along one `payoffChild` edge under well-formedness. -/
lemma payoffChild_lt_of_wellFormed {b : Blockchain n} (hw : b.WellFormed)
    (m : Miner n) {idx c : Nat} (hc : b.payoffChild m idx = some c)
    (hidx : idx < b.blocks.length) : idx < c ∧ c < b.blocks.length :=
  (mem_children_of_payoffChild hw m hc hidx).2

/-- Every `pathAux` list is nonempty and starts at its seed index. -/
lemma payoffPath_pathAux_head (b : Blockchain n) (m : Miner n) (fuel idx : Nat) :
    (Blockchain.payoffPath.pathAux b m fuel idx).head? = some idx := by
  cases fuel <;> simp [Blockchain.payoffPath.pathAux]

/-- If a list is strictly increasing and starts at `c`, every member is `≥ c`. -/
lemma le_of_mem_pairwise_lt {c y : Nat} {l : List Nat}
    (hhead : l.head? = some c) (hpw : l.Pairwise (· < ·)) (hy : y ∈ l) : c ≤ y := by
  match l with
  | [] => simp at hhead
  | z :: zs =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (List.rel_of_pairwise_cons hpw hy)

/-- The payoff path is pairwise strictly increasing, hence has no duplicates. -/
lemma payoffPath_nodup {b : Blockchain n} (hw : b.WellFormed) (m : Miner n)
    {idx : Nat} (hidx : idx < b.blocks.length) :
    (b.payoffPath m idx).Nodup := by
  suffices h :
      ∀ fuel idx,
        idx < b.blocks.length →
        (Blockchain.payoffPath.pathAux b m fuel idx).Pairwise (· < ·) ∧
          ∀ x ∈ Blockchain.payoffPath.pathAux b m fuel idx, x < b.blocks.length by
    exact (h b.blocks.length idx hidx).1.imp Nat.ne_of_lt
  intro fuel
  induction fuel with
  | zero =>
      intro idx hidx
      refine ⟨?_, ?_⟩
      · simp [Blockchain.payoffPath.pathAux]
      · intro x hx
        simp only [Blockchain.payoffPath.pathAux, List.mem_singleton] at hx
        simpa [hx] using hidx
  | succ fuel ih =>
      intro idx hidx
      simp only [Blockchain.payoffPath.pathAux]
      cases hc : b.payoffChild m idx with
      | none =>
          refine ⟨?_, ?_⟩
          · simp
          · intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            simpa [hx] using hidx
      | some c =>
          have hlt := payoffChild_lt_of_wellFormed hw m hc hidx
          have hpw_mem := ih c hlt.2
          refine ⟨?_, ?_⟩
          · rw [List.pairwise_cons]
            refine ⟨fun y hy => Nat.lt_of_lt_of_le hlt.1
              (le_of_mem_pairwise_lt (payoffPath_pathAux_head b m fuel c) hpw_mem.1 hy),
              hpw_mem.1⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hidx
            · exact hpw_mem.2 x hx

/-!
## Payoff is at most miner count (hence at most win count)
-/

/-- Number of blocks mined by `m` at indices greater than or equal to `idx`. -/
private def minerCountFrom (b : Blockchain n) (m : Miner n) (idx : Nat) : Nat :=
  (b.blocks.drop idx).countP (minedBy m)

/-- Moving the lower index forward cannot increase the count. -/
private lemma minerCountFrom_mono (b : Blockchain n) (m : Miner n) {i j : Nat}
    (h : i ≤ j) :
    minerCountFrom b m j ≤ minerCountFrom b m i :=
  (List.drop_sublist_drop_left b.blocks h).countP_le

/-- Split off the block at the current index. -/
private lemma minerCountFrom_step (b : Blockchain n) (m : Miner n) (idx : Nat)
    (hidx : idx < b.blocks.length) :
    minerCountFrom b m idx =
      (if minedBy m b.blocks[idx] then 1 else 0) + minerCountFrom b m (idx + 1) := by
  unfold minerCountFrom
  rw [← List.getElem_cons_drop hidx, List.countP_cons]
  omega

/-- The full miner count is the count from index `0`. -/
private lemma minerCountFrom_zero (b : Blockchain n) (m : Miner n) :
    minerCountFrom b m 0 = b.minerCount m := by
  simp [minerCountFrom, Blockchain.minerCount]

/-- Recursive payoff component equals the third field of an `earliestLongest` hit. -/
private lemma earliestLongest_payoff_eq (b : Blockchain n) (m : Miner n) (fuel : Nat)
    (children : List Nat) {c cl cp : Nat}
    (h : earliestLongest
        (children.map fun cidx =>
          let rest := Blockchain.payoff.payoffAux b m fuel cidx
          (cidx, rest.1, rest.2.2)) = some (c, cl, cp)) :
    cp = (Blockchain.payoff.payoffAux b m fuel c).2.2 ∧ c ∈ children := by
  have hmem := earliestLongest_mem _ h
  obtain ⟨cidx, hcidx, heq⟩ := List.mem_map.mp hmem
  have hc_eq : cidx = c := congrArg Prod.fst heq
  have hcp_eq : (Blockchain.payoff.payoffAux b m fuel cidx).2.2 = cp := by
    have := congrArg (fun p : Nat × Nat × Nat => p.2.2) heq
    simpa using this
  subst hc_eq
  exact ⟨hcp_eq.symm, hcidx⟩

/-- On a well-formed chain, `payoffAux` never exceeds `minerCountFrom` at `idx`. -/
private lemma payoffAux_le_minerCountFrom (b : Blockchain n) (hw : b.WellFormed)
    (m : Miner n) :
    ∀ fuel idx,
      idx < b.blocks.length →
      b.blocks.length - idx ≤ fuel →
      (Blockchain.payoff.payoffAux b m fuel idx).2.2 ≤ minerCountFrom b m idx := by
  intro fuel
  induction fuel with
  | zero =>
      intro idx hidx hfuel
      omega
  | succ fuel ih =>
      intro idx hidx hfuel
      simp only [Blockchain.payoff.payoffAux, List.getElem?_eq_getElem hidx]
      set block := b.blocks[idx]
      set own : Nat := if block.miner = some m then 1 else 0
      have hown : own = if minedBy m block then 1 else 0 := by
        simp [own, minedBy, block]
      cases hbest : earliestLongest
          (block.children.map fun cidx =>
            let rest := Blockchain.payoff.payoffAux b m fuel cidx
            (cidx, rest.1, rest.2.2)) with
      | none =>
          -- Payoff is just `own`, which is bounded by the count from `idx`.
          have hstep := minerCountFrom_step b m idx hidx
          cases hm : minedBy m block
          · simp [hown, hm]
          · simp [hown, hm, block, hstep]
      | some p =>
          obtain ⟨c, cl, cp⟩ := p
          obtain ⟨hcp_eq, hc_mem⟩ := earliestLongest_payoff_eq b m fuel block.children hbest
          obtain ⟨_, hch⟩ := hw
          have ⟨hlt, hc_lt⟩ := hch idx c hidx (by simpa [block] using hc_mem)
          have hfuel' : b.blocks.length - c ≤ fuel := by omega
          have hcp := ih c hc_lt hfuel'
          have hmono := minerCountFrom_mono b m (Nat.succ_le_of_lt hlt)
          have hstep := minerCountFrom_step b m idx hidx
          calc
            own + cp
                = own + (Blockchain.payoff.payoffAux b m fuel c).2.2 := by rw [hcp_eq]
            _ ≤ (if minedBy m block then 1 else 0) + minerCountFrom b m c := by
                  simpa [hown] using Nat.add_le_add_left hcp own
            _ ≤ (if minedBy m block then 1 else 0) + minerCountFrom b m (idx + 1) :=
                Nat.add_le_add_left hmono _
            _ = minerCountFrom b m idx := by
                  simpa [block] using hstep.symm

/-- On a well-formed chain, miner payoff from any in-range node is at most `minerCount`. -/
theorem payoff_le_minerCount {b : Blockchain n} (hw : b.WellFormed) (m : Miner n)
    {idx : Nat} (hidx : idx < b.blocks.length) :
    (b.payoff m idx).2.2 ≤ b.minerCount m := by
  have hfuel : b.blocks.length - idx ≤ b.blocks.length := by omega
  have h := payoffAux_le_minerCountFrom b hw m b.blocks.length idx hidx hfuel
  exact h.trans <| (minerCountFrom_mono b m (Nat.zero_le idx)).trans_eq (minerCountFrom_zero b m)

/-- After any finite execution, strategy-sequence payoff is at most lottery wins. -/
theorem strategySequencePayoff_le_winCount (σ : MinerStrategyProfile n) (k : Nat)
    (draws : Fin k → Miner n) (m : Miner n) :
    strategySequencePayoff σ k draws m ≤ winCount draws m := by
  have hw := wellFormed_execution σ k draws
  have hidx : (0 : Nat) < (execution σ k draws).blocks.length := by
    have := hw.1
    exact List.length_pos_of_ne_nil this
  have hpay := payoff_le_minerCount hw m hidx
  have hmc := minerCount_le_winCount σ k draws m
  exact (hpay.trans hmc)

/-!
## A concrete forked chain

Three miners; main spine of length 4 with a one-block fork off depth 2:

```
0 (genesis)
└─ 1 (miner 0)           -- depth 2
   ├─ 2 (miner 0)
   │  └─ 3 (miner 1)
   └─ 4 (miner 2)         -- fork tip
```

Longest-chain payoff from genesis follows `0-1-2-3`, so miner 2 (only on the
short fork) scores `0`.
-/

def exampleForkChain : Blockchain 3 where
  blocks := [
    { miner := none, children := [1] },
    { miner := some 0, children := [2, 4] },
    { miner := some 0, children := [3] },
    { miner := some 1, children := [] },
    { miner := some 2, children := [] }
  ]

example : (exampleForkChain.payoff (0 : Fin 3) 0).2.2 = 2 := by decide
example : (exampleForkChain.payoff (1 : Fin 3) 0).2.2 = 1 := by decide
example : (exampleForkChain.payoff (2 : Fin 3) 0).2.2 = 0 := by decide

end MathEconLibExamples.GameTheory.FiniteBlockchainGames
end
