import ExtrDisc.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.Zorn

open CategoryTheory

variable {A : Type _} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ExtremallyDisconnected A]
variable {B C : Type _} [TopologicalSpace B] [TopologicalSpace C] [T2Space B] [T2Space C]
  [CompactSpace B] [CompactSpace C]
variable (φ : A → C) (f : B → C)

def D : Set (A × B) := {x | φ x.fst = f x.snd}

def π₁ : D φ f → A := fun x ↦ x.val.fst

def π₂ : D φ f → B := fun x ↦ x.val.snd

variable {φ} {f} (hφ : Continuous φ) (hf : Continuous f) (hf' : f.Surjective)

instance one : CompactSpace (D φ f) :=
isCompact_iff_compactSpace.mp (IsClosed.isCompact
  (isClosed_eq (Continuous.comp hφ continuous_fst) (Continuous.comp hf continuous_snd )))

lemma two : (π₁ φ f).Surjective := by
  intro a
  obtain ⟨b, hb⟩ := hf' (φ a)
  use ⟨(a,b), hb.symm⟩
  rfl

lemma two_half : Continuous (π₁ φ f) := by
  sorry

lemma three : ∃ (E : Set (D φ f)), CompactSpace E ∧ (π₁ φ f) '' E = Set.univ ∧ ∀ (E₀ : Set (D φ f)),
    E₀ ⊂ E → CompactSpace E₀ → ¬ ((π₁ φ f)'' E₀) = Set.univ := by
  -- Define the set of closed subsets of D for which the map onto A is surjective
  let S := { E : Set (D φ f) | CompactSpace E ∧ (π₁ φ f) '' E = Set.univ}
  -- Checking the Chain condition
  have chain_cond : (∀ (c : Set (Set ↑(D φ f))),
      c ⊆ S →
      IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D φ f)), s ∈ c → lb ⊆ s) := by
    intro Ch h hCh
    let M := Set.sInter Ch
    use M
    constructor
    · constructor
      · rw [←isCompact_iff_compactSpace]
        apply @IsClosed.isCompact _ _ (one hφ hf)
        apply isClosed_sInter
        intro N hN
        have N_comp := (h hN).1
        dsimp at N_comp
        rw [←isCompact_iff_compactSpace] at N_comp
        exact IsCompact.isClosed N_comp
      --Next, we need to show that the image of M is all of A
      · by_cases h₂ : Nonempty Ch
        rotate_left 1
        -- Case that `Ch` is empty
        · simp at h₂
          rw [←Set.eq_empty_iff_forall_not_mem] at h₂
          revert M
          rw [h₂, Set.sInter_empty]
          simp
          have : (π₁ φ f).Surjective := two hf'
          exact Iff.mpr Set.range_iff_surjective this
        -- Now we assume that `Ch` is nonempty
        · ext x
          refine' ⟨ fun _ => trivial , fun _ => _ ⟩
          rw [Set.mem_image]
          change Set.Nonempty {x_1 : D φ f | x_1 ∈ M ∧ π₁ φ f x_1 = x}
          let Z : Ch → Set (D φ f) := fun X => X ∩ (π₁ _ _)⁻¹' {x}
          suffices Set.Nonempty <| ⋂ (X : Ch), (X: Set (D φ f)) ∩ (π₁ _ _)⁻¹' {x} by
            convert this
            rw [← Set.iInter_inter, ←  Set.sInter_eq_iInter]
            rw [←Set.setOf_inter_eq_sep, Set.inter_comm]
            congr
          -- Using this result `nonempty_iInter_of_...` introduces a lot of unnecessary checks
          have assumps : ∀ (i : ↑Ch), Set.Nonempty (Z i) ∧ IsCompact (Z i) ∧ IsClosed (Z i) := by
            intro X
            -- `Z X` nonempty
            simp
            have h₃ := (h (Subtype.mem X)).2
            rw [←Set.image_inter_nonempty_iff, h₃]
            simp
            -- `Z X` is Closed
            have := (h (Subtype.mem X)).1
            rw [←isCompact_iff_compactSpace] at this
            have h_cl := IsClosed.inter (IsCompact.isClosed this)
                (IsClosed.preimage two_half <| T1Space.t1 x)
            exact And.intro (@IsClosed.isCompact _ _ (one hφ hf) _ h_cl) h_cl

          apply IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed Z _
              (fun X => (assumps X).1) (fun X => (assumps X).2.1) (fun X => (assumps X).2.2)
        -- Need to show the `Directed` assumption for the inclusion, which is annoying...
          · intro X Y
            have hCh₂ := hCh X.2 Y.2
            by_cases X.1 = Y.1
            · use X
              simp
              rw [h]
              simp
            replace hCh₂ := hCh₂ h
            apply Or.elim hCh₂
            · intro h_left
              use X
              simp
              apply ((Set.inter_subset_left _ _).trans h_left)
            · intro h_right
              use Y
              simp
              apply ((Set.inter_subset_left _ _).trans h_right)
    · intro X hX
      exact Set.sInter_subset_of_mem hX
  have := zorn_superset S chain_cond
  rcases this with ⟨E, ⟨⟨hE₁,hE₂⟩, hE₃⟩⟩
  use E
  constructor
  · exact hE₁
  constructor
  · exact hE₂
  --Now, it's just rephrasing the conclusion of Zorn's Lemma
  · intro E₀ h₁ h₂
    replace hE₃ := hE₃ E₀
    by_contra h₃
    replace hE₃ := hE₃ (And.intro h₂ h₃) (subset_of_ssubset h₁)
    exact (ne_of_ssubset h₁) hE₃


def E : (Set (D φ f)) := (three hφ hf hf').choose

lemma gleason21 (X Y : Type _) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {g : X → Y} (hg_cong : Continuous g) (hg_surj : g.Surjective) (hg : ∀ (E₀ : Set X), ¬ E₀ = ⊤ →
    IsClosed E₀ → ¬ (g '' E₀ = ⊤)) : ∀ U : Set X, IsOpen U → (g '' U) ⊆ closure ((g '' (Uᶜ))ᶜ) :=
sorry

lemma gleason22 {E₁ E₂ : Set A} (h : Disjoint E₁ E₂) (h₁ : IsOpen E₁) (h₂ : IsOpen E₂) :
    Disjoint (closure E₁) (closure E₂) :=
  Disjoint.closure_left (Disjoint.closure_right h h₁) (ExtremallyDisconnected.open_closure E₂ h₂)

lemma gleason23_inj (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
  (hr_surj: r.Surjective) (hE : CompactSpace E)
  (h_subsets : ∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) : r.Injective := by
  · rw [Function.Injective]
    intros x y h_eq_im
    by_contra h
    rcases t2_separation h with ⟨G₁, G₂, hG₁, hG₂, hxG₁, hyG₂, hG⟩
    have open1 : IsOpen ((r '' (G₁ᶜ))ᶜ)
    · simp only [isOpen_compl_iff]
      apply IsCompact.isClosed
      refine' IsCompact.image (IsClosed.isCompact _) hr
      simpa only [isClosed_compl_iff]
    have open2 : IsOpen ((r '' (G₂ᶜ))ᶜ)
    · simp only [isOpen_compl_iff]
      apply IsCompact.isClosed
      refine' IsCompact.image (IsClosed.isCompact _) hr
      simpa only [isClosed_compl_iff]
    have disj : Disjoint ((r '' (G₁ᶜ))ᶜ) ((r '' (G₂ᶜ))ᶜ)
    · rw [Set.disjoint_compl_left_iff_subset]
      refine' subset_trans (Set.subset_image_compl hr_surj) _
      simp only [compl_compl, Set.image_subset_iff]
      refine' subset_trans _ (Set.subset_preimage_image _ _)
      rw [← Set.disjoint_compl_left_iff_subset]
      simpa only [compl_compl]
    replace disj := gleason22 disj open1 open2
    have oups₁ := gleason21 E A hr hr_surj h_subsets G₁ hG₁
    have oups₂ := gleason21 E A hr hr_surj h_subsets G₂ hG₂
    have mem₁ : r x ∈ r '' G₁
    · exact Set.mem_image_of_mem _ hxG₁
    have mem₂ : r x ∈ r '' G₂
    · rw [h_eq_im]
      exact Set.mem_image_of_mem _ hyG₂
    have mem : r x ∈ (closure ((r '' G₁ᶜ)ᶜ)) ∩ (closure ((r '' G₂ᶜ)ᶜ)) := ⟨oups₁ mem₁, oups₂ mem₂⟩
    exact (disj.ne_of_mem mem.1 mem.2) rfl

lemma gleason23_surj : ((E hφ hf hf').restrict (π₁ φ f)).Surjective := by
  intro a
  have := (three hφ hf hf').choose_spec.2.1
  have ha : a ∈ Set.univ := by tauto
  rw [← this] at ha
  obtain ⟨c,hc⟩ := ha
  use ⟨c,hc.1⟩
  exact hc.2

lemma gleason23_cont (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
    (hr_surj: r.Surjective) (hE : CompactSpace E)
    (h_subsets : ∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) :
    Continuous (Function.Embedding.equivOfSurjective
    ⟨r, gleason23_inj E hr hr_surj hE h_subsets⟩ hr_surj) := hr

lemma gleason23_cont' : Continuous ((E hφ hf hf').restrict (π₁ φ f)) :=
ContinuousOn.restrict (Continuous.continuousOn (Continuous.comp continuous_fst
  continuous_subtype_val))

noncomputable
def gleason23_def (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
  (hr_surj: r.Surjective) (hE : CompactSpace E)
  (h_subsets : ∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) : E ≃ₜ A :=
Continuous.homeoOfEquivCompactToT2 (gleason23_cont E hr hr_surj hE h_subsets)

noncomputable
def ρ : (E hφ hf hf') ≃ₜ A := by
  refine' gleason23_def (E hφ hf hf') (gleason23_cont' hφ hf hf') (gleason23_surj hφ hf hf')
    (three hφ hf hf').choose_spec.1 _
  sorry -- we need to decide what to do with `three` etc. to resolve this
-- where
--   toFun := (E hφ hf).restrict (π₁ φ f)
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry
--   continuous_toFun := sorry
--   continuous_invFun := sorry

lemma five : Continuous ((E hφ hf hf').restrict (π₂ φ f) ∘ (ρ hφ hf hf').invFun) ∧
  f ∘ ((E hφ hf hf').restrict (π₂ φ f) ∘ (ρ hφ hf hf').invFun) = φ := sorry

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected A.compHaus.toTop := A.extrDisc
    use ⟨_, (five φ.continuous f.continuous sorry).left⟩
    ext
    exact congr_fun (five φ.continuous f.continuous sorry).right _