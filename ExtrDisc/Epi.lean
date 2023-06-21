import ExtrDisc.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

open CategoryTheory TopologicalSpace

namespace ExtrDisc

universe u

def two : ExtrDisc.{u} where
  compHaus := CompHaus.of <| ULift <| Fin 2
  projective := sorry

lemma epi_iff_surjective {X Y : ExtrDisc.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y,hy⟩ h
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hC.compl_mem_nhds hyU
    haveI : TotallyDisconnectedSpace ((forget CompHaus).obj (toCompHaus.obj Y)) := 
      show TotallyDisconnectedSpace Y from inferInstance
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_clopen.mem_nhds_iff.mp hUy
    classical
    let g : Y ⟶ two :=  ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩ 
    let h : Y ⟶ two := ⟨fun _ => ⟨1⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      apply ContinuousMap.ext ; intro x
      apply ULift.ext
      change 1 =  _
      dsimp [LocallyConstant.ofClopen]
      rw [comp_apply, ContinuousMap.coe_mk, Function.comp_apply, if_neg]
      refine' mt (fun α => hVU α) _
      simp only [Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      exact ⟨x, rfl⟩  
    apply_fun fun e => (e y).down at H
    dsimp [LocallyConstant.ofClopen] at H
    change 1 = ite _ _ _ at H
    rw [if_pos hyV] at H
    exact top_ne_bot H
  · intro (h : Function.Surjective (toCompHaus.map f))
    rw [← CompHaus.epi_iff_surjective] at h
    constructor
    intro W a b h
    apply Functor.map_injective toCompHaus
    apply_fun toCompHaus.map at h
    simp only [Functor.map_comp] at h
    rwa [← cancel_epi (toCompHaus.map f)]

open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : ExtrDisc.{u}} 
    (X : α → ExtrDisc.{u})
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b 
    ] := by
  tfae_have 1 → 2 
  · intro ; infer_instance 
  tfae_have 2 → 3
  · sorry 
  tfae_have 3 → 1
  · sorry
  tfae_finish

end ExtrDisc