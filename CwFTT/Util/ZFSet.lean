import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic

universe u

namespace ZFSet

-- by virtue of writing `x.pair y ∈ f`, we automatically assume x ∈ X and y ∈ Y


lemma IsFunc.congr {X Y f : ZFSet.{u}} (hf : IsFunc X Y f) {x y y' : ZFSet.{u}}
    (hy : x.pair y ∈ f) (hy' : x.pair y' ∈ f) : y = y' := by
  -- dsimp [IsFunc] at hf
  have hx : x ∈ X :=
    (pair_mem_prod.mp (hf.left hy)).left
  exact (hf.right x hx).unique hy hy'

lemma congr_arg {X Y : ZFSet.{u}} (f : X.funs Y) {x x' y y' : ZFSet.{u}}
    (hx : x.pair y ∈ f.val) (hx' : x'.pair y' ∈ f.val) : x = x' → y = y' := by
  rintro rfl
  exact (mem_funs.mp f.prop).congr hx hx'

lemma subset_ext {X Y Z : ZFSet.{u}} (hX : X ⊆ Z) (hY : Y ⊆ Z) :
    (∀ x ∈ Z, (x ∈ X ↔ x ∈ Y)) → X = Y := by
  intro hext
  ext z
  constructor
  · intro hzX
    exact (hext z (hX hzX)).mp hzX
  · intro hzY
    exact (hext z (hY hzY)).mpr hzY

lemma funs.ext {X Y : ZFSet.{u}} {f g : X.funs Y}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x.pair y ∈ f.val ↔ x.pair y ∈ g.val) : f = g := by
  ext1
  apply subset_ext (mem_powerset.mp (mem_sep.mp f.prop).left)
    (mem_powerset.mp (mem_sep.mp g.prop).left)
  simp only [mem_prod, forall_exists_index, and_imp]
  rintro _ x hx y hy rfl
  exact h x hx y hy

section comp

/-- the relational set -/
private def funs.comp' {X Y Z : ZFSet.{u}} (f : X.funs Y) (g : Y.funs Z) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x z : ZFSet.{u},
    (p = x.pair z ∧ ∃ y, x.pair y ∈ f.val ∧ y.pair z ∈ g.val)) (X.prod Z)

@[simp]
private lemma mem_comp' {X Y Z : ZFSet.{u}} (f : X.funs Y) (g : Y.funs Z)
  {x z : ZFSet.{u}} : x.pair z ∈ funs.comp' f g ↔
    ∃ y, x.pair y ∈ f.val ∧ y.pair z ∈ g.val := by
  simp [funs.comp']
  intro y hy₁ hy₂
  use (pair_mem_prod.mp ((mem_funs.mp f.prop).left hy₁)).left
  exact (pair_mem_prod.mp ((mem_funs.mp g.prop).left hy₂)).right

lemma funs.comp'_mem {X Y Z : ZFSet.{u}} (f : X.funs Y) (g : Y.funs Z)
  : funs.comp' f g ∈ X.funs Z := by
  have hf := f.property
  have hg := g.property
  rw [mem_funs] at hf hg ⊢
  dsimp [IsFunc] at hf hg ⊢
  use (ZFSet.sep_subset)
  intro x hx
  apply (hf.right x hx).elim
  intro y hy₁ hy_eq
  have hy₂ := hf.left hy₁
  rw [ZFSet.pair_mem_prod] at hy₂
  apply (hg.right y (hy₂.right)).imp
  dsimp
  intro z ⟨hz₁,hz_eq⟩
  have hz₂ := (hg.left hz₁)
  rw [ZFSet.pair_mem_prod] at hz₂
  constructor
  · rw [mem_comp']
    use y
  · intro z' hz'
    rw [mem_comp'] at hz'
    obtain ⟨y,hy',hy''⟩ := hz'
    -- obtain rfl := congr_arg f hy₁ hy' rfl
    exact (congr_arg g hz₁ hy'' (congr_arg f hy₁ hy' rfl)).symm

def funs.comp {X Y Z : ZFSet.{u}} (f : X.funs Y) (g : Y.funs Z) :
  X.funs Z := ⟨funs.comp' f g,comp'_mem f g⟩

lemma mem_comp {X Y Z : ZFSet.{u}} (f : X.funs Y) (g : Y.funs Z) {x z : ZFSet.{u}} :
    x.pair z ∈ (funs.comp f g).val ↔ ∃ y, (x.pair y ∈ f.val ∧ y.pair z ∈ g.val) := by
  rw [funs.comp,mem_comp']

@[simp]
lemma comp_assoc {W X Y Z : ZFSet.{u}} (f : W.funs X) (g : X.funs Y) (h : Y.funs Z) :
  funs.comp (funs.comp f g) h = funs.comp f (funs.comp g h) := by
  apply funs.ext
  intro w hw z hz
  simp_rw [mem_comp,← exists_and_right,
    ← exists_and_left, and_assoc]
  rw [exists_comm]

end comp

section id

def id_ (X : ZFSet.{u}) : X.funs X :=
  ⟨ZFSet.sep (fun z => ∃ x : ZFSet.{u}, z = x.pair x) (X.prod X), by
    rw [mem_funs]
    use sep_subset
    simp [ExistsUnique]⟩

lemma mem_id {X : ZFSet.{u}} (x y : ZFSet.{u}) : x.pair y ∈ (id_ X).val ↔
  x ∈ X ∧ x = y := by unfold id_; aesop

@[simp]
lemma comp_id {X Y : ZFSet.{u}} (f : X.funs Y) :
    funs.comp f (id_ Y) = f := by
  apply funs.ext
  intro x hx y hy
  simp [mem_comp, mem_id, hy]

@[simp]
lemma id_comp {X Y : ZFSet.{u}} (f : X.funs Y) :
    funs.comp (id_ X) f = f := by
  apply funs.ext
  rintro x hx y hy
  simp [mem_comp, mem_id, hx]


end id

section app
noncomputable def funs.app {X Y : ZFSet.{u}} (f : X.funs Y) (x : X) : Y :=
  ⟨((mem_funs.mp f.prop).right x x.prop).choose, by
    generalize_proofs h
    simpa using (mem_funs.mp f.prop).left (h.choose_spec.left)⟩

lemma pair_app_mem {X Y : ZFSet.{u}} (f : X.funs Y) (x : X) :
    x.val.pair (funs.app f x).val ∈ f.val := by
  rw [funs.app]
  generalize_proofs h1 h2
  exact h1.choose_spec.left

lemma app_eq_iff {X Y : ZFSet.{u}} (f : X.funs Y) (x : X) (y : ZFSet.{u}) :
    funs.app f x = y ↔ x.val.pair y ∈ f.val := by
  constructor
  · rintro rfl
    exact pair_app_mem f x
  · exact ((mem_sep.mp f.prop).right.right x x.prop).unique (pair_app_mem f x)

lemma app_comp {X Y Z : ZFSet.{u}} (f : X.funs Y) (g : Y.funs Z) :
  funs.app (funs.comp f g) = funs.app g ∘ (funs.app f) := by
  ext x : 2
  rw [app_eq_iff,Function.comp_apply,mem_comp]
  use funs.app f x, (pair_app_mem _ _), (pair_app_mem _ _)

lemma app_id (X : ZFSet.{u}) : funs.app (id_ X) = id := by
  ext x : 2
  rw [app_eq_iff, mem_id]
  use x.prop
  exact rfl

private def ofFun' {X Y : ZFSet.{u}} (f : X → Y) : ZFSet :=
  ZFSet.sep (fun z => ∃ x y, x.pair y = z ∧ ∃ (hx : x ∈ X), y = (f ⟨x,hx⟩).val) (X.prod Y)

def ofFun {X Y : ZFSet.{u}} (f : X → Y) : X.funs Y :=
  ⟨ofFun' f,by
    rw [mem_funs]
    constructor
    · exact sep_subset
    · intro x hx
      use f ⟨x,hx⟩
      simp only [ofFun', ↓existsAndEq, and_true, mem_sep, mem_prod, pair_inj,
        exists_eq_right_right', SetLike.coe_mem, true_and, exists_eq_right', hx, SetLike.coe_eq_coe,
        exists_and_left, exists_eq_left, exists_const, and_self, exists_true_left, and_imp]
      intro y hy heq
      exact heq.symm
    ⟩

lemma mem_ofFun {X Y : ZFSet.{u}} (f : X → Y) {x y : ZFSet.{u}} :
    x.pair y ∈ (ofFun f).val ↔ ∃ (h : x ∈ X), f ⟨x,h⟩ = y := by
  rw [ofFun]
  simp +contextual only [ofFun', ↓existsAndEq, and_true, mem_sep, mem_prod, pair_inj,
    exists_eq_right_right', exists_and_left, exists_eq_left, and_iff_right_iff_imp,
    forall_exists_index, true_and]
  intro hx h
  rw [← h]
  exact (f ⟨x,hx⟩).prop

noncomputable def funs_equiv {X Y : ZFSet.{u}} : X.funs Y ≃ (X → Y) where
  toFun := funs.app
  invFun := ofFun
  left_inv f := by
    apply funs.ext
    intro x hx y hy
    simp [mem_ofFun, app_eq_iff, hx]
  right_inv g := by
    ext x : 2
    rw [app_eq_iff, mem_ofFun]
    use x.prop

end app

end ZFSet

open ZFSet
@[ext]
structure ZFSet.Hom (X Y : ZFSet.{u}) where
  ofFunc ::
    toFunc : X.funs Y

namespace CategoryTheory

instance : Category (ZFSet.{u}) where
  Hom X Y := ZFSet.Hom X Y
  id X := Hom.ofFunc (id_ X)
  comp {X Y Z} f g := .ofFunc (funs.comp f.toFunc g.toFunc)

def ZFSet.toTypesObj (s : ZFSet.{u}) : Type u :=
  s.card.out

noncomputable def ZFSet.toTypesObjEquiv (s : ZFSet.{u}) : s ≃
  toTypesObj s := by
  apply Classical.choice
  rw [← Cardinal.lift_mk_eq.{u+1,u,u+1}]
  simpa [toTypesObj] using cardinalMk_coe_sort

noncomputable def ZFSet.toTypes' : ZFSet.{u} ⥤ Type (u + 1) where
  obj X := X
  map {X Y} f := funs.app f.toFunc
  map_id X := by
    dsimp [(𝟙 ·)]
    exact app_id X
  map_comp {X Y Z} f g := by
    dsimp [(· ≫ ·)]
    exact app_comp f.toFunc g.toFunc

noncomputable def ZFSet.toTypes : ZFSet.{u} ⥤ (Type u) where
  obj X := toTypesObj X
  map {X Y} f := ((toTypesObjEquiv Y) ∘ (funs_equiv f.toFunc) ∘ (toTypesObjEquiv X).symm)
  map_id X := by
    simp [(𝟙 ·), funs_equiv, app_id]
  map_comp {X Y Z} f g := by
    dsimp [(· ≫ ·)]
    ext x
    simp [funs_equiv, app_comp, Function.comp_assoc]

instance ZFSet.toTypes.full : (ZFSet.toTypes.{u}).Full where
  map_surjective {X Y} := by
    intro f
    use .ofFunc (funs_equiv.symm <| (toTypesObjEquiv Y).symm ∘ f ∘ (toTypesObjEquiv X))
    ext x
    simp [toTypes]

instance ZFSet.toTypes.faithful : (ZFSet.toTypes.{u}).Faithful where
  map_injective {X Y} := by
    intro f g
    simp only [toTypes]
    intro h
    have : funs_equiv f.toFunc = funs_equiv g.toFunc := by
      ext x : 1
      simpa using congr((toTypesObjEquiv Y).symm ($h (toTypesObjEquiv X x)))
    exact congr(ZFSet.Hom.ofFunc $(funs_equiv.injective this))

instance ZFSet.toTypes.essSurj : (ZFSet.toTypes.{u}).EssSurj where
  mem_essImage Y := by
    dsimp [Functor.essImage]


end CategoryTheory
