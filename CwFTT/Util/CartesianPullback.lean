import CwFTT.Util.Cartesian
import CwFTT.Util.Pullback

universe v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
open Limits MonoidalCategory CartesianMonoidalCategory

lemma _root_.CategoryTheory.IsPullback.tensor {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₁ ⟶ Y₃} {g₃ : Y₂ ⟶ Y₄} {g₄ : Y₃ ⟶ Y₄} (hg : IsPullback g₁ g₂ g₃ g₄) :
    IsPullback (tensorHom f₁ g₁) (tensorHom f₂ g₂) (tensorHom f₃ g₃) (tensorHom f₄ g₄) := by
  refine ⟨⟨?_⟩,⟨?_⟩⟩
  · simp [hf.w,hg.w]
  · refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      have := s.condition
      simp only [CartesianMonoidalCategory.hom_ext_iff, Category.assoc, tensorHom_fst,
        tensorHom_snd] at this
      apply lift
      · fapply hf.lift (s.fst ≫ fst _ _) (s.snd ≫ fst _ _)
        simpa using this.left
      · fapply hg.lift (s.fst ≫ snd _ _) (s.snd ≫ snd _ _)
        simpa using this.right
    · intro s
      simp
    · intro s
      simp
    · intro s m hm₁ hm₂
      simp_all [CartesianMonoidalCategory.hom_ext_iff]
      constructor
      · apply hf.hom_ext
        · simpa using hm₁.left
        · simpa using hm₂.left
      · apply hg.hom_ext
        · simpa using hm₁.right
        · simpa using hm₂.right





end CategoryTheory
