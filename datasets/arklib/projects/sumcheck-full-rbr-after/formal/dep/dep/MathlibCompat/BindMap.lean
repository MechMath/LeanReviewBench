/- Original Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0. -/
module
public import Mathlib.MeasureTheory.Measure.GiryMonad
@[expose] public section
open MeasureTheory
namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
theorem bind_map {γ} [MeasurableSpace γ] {m : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.map f)) :
    bind (map f m) g = bind m fun a ↦ g (f a) := by
  ext1 s hs
  have h' : AEMeasurable (fun b ↦ g b s) (map f m) := (measurable_coe hs).comp_aemeasurable hg
  rw [bind_apply hs hg, lintegral_map' (by fun_prop) hf, bind_apply hs (by fun_prop)]
end MeasureTheory.Measure
