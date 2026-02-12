import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

universe u
variable
    {𝓒 : Type u}
    [CategoryTheory.Category 𝓒]
    {U V W X Y Z P T : 𝓒}

namespace CategoryTheory.Limits

section prod

variable
    (fst : P ⟶ X)
    (snd : P ⟶ Y)

def IsBinaryProduct :=
  IsLimit (BinaryFan.mk fst snd)

def IsBinaryProduct.ofUniqueHom {fst snd}
    (lift : {T : 𝓒} → (T ⟶ X) → (T ⟶ Y) → (T ⟶ P))
    (hl₁ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ fst = f)
    (hl₂ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ snd = g)
    (uniq : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ P), m ≫ fst = f → m ≫ snd = g → m = lift f g)
    : IsBinaryProduct fst snd :=
  BinaryFan.IsLimit.mk _ lift hl₁ hl₂ uniq

theorem IsBinaryProduct.hasBinaryProduct (h : IsBinaryProduct fst snd) : HasBinaryProduct X Y :=
  ⟨⟨{ cone := BinaryFan.mk fst snd, isLimit := h }⟩⟩

variable {fst snd}

def IsBinaryProduct.lift
    (h : IsBinaryProduct fst snd)
    {T : 𝓒}
    (f : T ⟶ X)
    (g : T ⟶ Y)
    : T ⟶ P :=
  IsLimit.lift h { pt := T, π := mapPair f g}

@[simp]
theorem IsBinaryProduct.ofUniqueHom_lift {fst snd}
    {lift : {T : 𝓒} → (T ⟶ X) → (T ⟶ Y) → (T ⟶ P)}
    {hl₁ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ fst = f}
    {hl₂ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ snd = g}
    {uniq : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ P), m ≫ fst = f → m ≫ snd = g → m = lift f g}
    : (ofUniqueHom lift hl₁ hl₂ uniq).lift = (lift : (T ⟶ X) → (T ⟶ Y) → (T ⟶ P)) := rfl

@[simp]
theorem IsBinaryProduct.lift_fst
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    : h.lift f g ≫ fst = f :=
  h.fac { pt := T, π := mapPair f g } (.mk .left)

@[simp]
theorem IsBinaryProduct.lift_snd
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    : h.lift f g ≫ snd = g :=
  h.fac { pt := T, π := mapPair f g } (.mk .right)

theorem IsBinaryProduct.uniq
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    (m : T ⟶ P)
    (hf : m ≫ fst = f)
    (hg : m ≫ snd = g)
    : m = h.lift f g :=
  IsLimit.uniq h { pt := T, π := mapPair f g } m fun
    | .mk .left => hf
    | .mk .right => hg

def IsBinaryProduct.map
    (fst : P ⟶ X)
    (snd : P ⟶ Y)
    {P' X' Y' : 𝓒}
    {fst' : P' ⟶ X'}
    {snd' : P' ⟶ Y'}
    (hg : IsBinaryProduct fst' snd')
    (f : X ⟶ X')
    (g : Y ⟶ Y')
    : P ⟶ P' :=
  hg.lift (fst ≫ f) (snd ≫ g)

theorem IsBinaryProduct.hom_ext
    (h : IsBinaryProduct fst snd)
    {f g : T ⟶ P}
    (hl : f ≫ fst = g ≫ fst)
    (hr : f ≫ snd = g ≫ snd)
    : f = g :=
  BinaryFan.IsLimit.hom_ext h hl hr

@[simp]
theorem IsBinaryProduct.lift_fst_snd
    (h : IsBinaryProduct fst snd)
    : h.lift fst snd = 𝟙 _ :=
  h.hom_ext
    ((h.lift_fst _ _).trans (Category.id_comp _).symm)
    ((h.lift_snd _ _).trans (Category.id_comp _).symm)

@[simp]
theorem IsBinaryProduct.lift_comp 
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    (v : V ⟶ T)
    : v ≫ h.lift f g = h.lift (v ≫ f) (v ≫ g) :=
  h.hom_ext
    (by simp)
    (by simp)

def IsBinaryProduct.iso
    {X Y P₁ P₂ : 𝓒}
    {fst₁ : P₁ ⟶ X} {snd₁ : P₁ ⟶ Y}
    {fst₂ : P₂ ⟶ X} {snd₂ : P₂ ⟶ Y}
    (h₁ : IsBinaryProduct fst₁ snd₁)
    (h₂ : IsBinaryProduct fst₂ snd₂)
    : P₁ ≅ P₂ where
  hom := h₂.lift fst₁ snd₁
  inv := h₁.lift fst₂ snd₂
  hom_inv_id := hom_ext h₁ (by simp) (by simp)
  inv_hom_id := hom_ext h₂ (by simp) (by simp)

def IsBinaryProduct.leftUnitor
    {X P T : 𝓒}
    (it : IsTerminal T)
    {tfst : P ⟶ T} {tsnd : P ⟶ X}
    (h : IsBinaryProduct tfst tsnd)
    : P ≅ X where
  hom := tsnd
  inv := h.lift (it.from _) (𝟙 X)
  hom_inv_id := by
    apply h.hom_ext
    · simp only [lift_comp, IsTerminal.comp_from, Category.comp_id, lift_fst, Category.id_comp]
      exact IsTerminal.hom_ext it (it.from P) tfst
    · simp
  inv_hom_id := by simp

def IsBinaryProduct.rightUnitor
    {X P T : 𝓒}
    (it : IsTerminal T)
    {tfst : P ⟶ X} {tsnd : P ⟶ T}
    (h : IsBinaryProduct tfst tsnd)
    : P ≅ X where
  hom := tfst
  inv := h.lift (𝟙 X) (it.from _)
  hom_inv_id := by
    apply h.hom_ext
    · simp 
    · simp only [lift_comp, Category.comp_id, IsTerminal.comp_from, lift_snd, Category.id_comp]
      exact IsTerminal.hom_ext it (it.from P) tsnd
  inv_hom_id := by simp

def IsBinaryProduct.associator
    {A B C AB BC AB_C A_BC : 𝓒}

    {aba : AB ⟶ A} {abb : AB ⟶ B}
    {bcb : BC ⟶ B} {bcc : BC ⟶ C}

    {ab_c_ab : AB_C ⟶ AB} {ab_c_c : AB_C ⟶ C}
    {a_bc_a : A_BC ⟶ A} {a_bc_bc : A_BC ⟶ BC}
    (h_AB : IsBinaryProduct aba abb)
    (h_BC : IsBinaryProduct bcb bcc)
    (h_AB_C : IsBinaryProduct ab_c_ab ab_c_c)
    (h_A_BC : IsBinaryProduct a_bc_a a_bc_bc)
    : AB_C ≅ A_BC where
  hom := h_A_BC.lift (ab_c_ab ≫ aba) (h_BC.lift (ab_c_ab ≫ abb) ab_c_c)
  inv := h_AB_C.lift (h_AB.lift a_bc_a (a_bc_bc ≫ bcb)) (a_bc_bc ≫ bcc)
  hom_inv_id := by
    apply h_AB_C.hom_ext
    · apply h_AB.hom_ext
      <;> simp only [lift_comp, lift_fst, Category.id_comp, lift_snd, Category.id_comp]
      rw [←Category.assoc]
      simp
    · simp only [lift_comp, lift_fst, lift_snd, Category.id_comp]
      rw [←Category.assoc]
      simp
  inv_hom_id := by
    apply h_A_BC.hom_ext
    · simp only [lift_comp, lift_snd, lift_fst, Category.id_comp]
      rw [←Category.assoc]
      simp

    · apply h_BC.hom_ext
      <;> simp only [lift_comp, lift_snd, lift_fst, Category.id_comp]
      rw [←Category.assoc]
      simp

noncomputable def productIsBinaryProduct [p : HasBinaryProduct X Y]
    : IsBinaryProduct (prod.fst : X ⨯ Y ⟶ X) prod.snd :=
  prodIsProd X Y

end prod

section coprod

variable
    (inl : X ⟶ P)
    (inr : Y ⟶ P)

def IsBinaryCoproduct :=
  IsColimit (BinaryCofan.mk inl inr)

def IsBinaryCoproduct.ofUniqueHom {inl inr}
    (desc : {T : _} → (X ⟶ T) → (Y ⟶ T) → (P ⟶ T))
    (hd₁ : ∀ {T : _} (f : X ⟶ T) (g : Y ⟶ T), inl ≫ desc f g = f)
    (hd₂ : ∀ {T : _} (f : X ⟶ T) (g : Y ⟶ T), inr ≫ desc f g = g)
    (uniq : ∀ {T : _} (f : X ⟶ T) (g : Y ⟶ T) (m : P ⟶ T), inl ≫ m = f → inr ≫ m = g → m = desc f g)
    : IsBinaryCoproduct inl inr :=
  BinaryCofan.IsColimit.mk _ desc  hd₁ hd₂ uniq

theorem IsBinaryCoproduct.hasBinaryCoproduct
    (h : IsBinaryCoproduct inl inr)
    : HasBinaryCoproduct X Y :=
  ⟨⟨{ cocone := BinaryCofan.mk inl inr, isColimit := h }⟩⟩

variable {inl inr}

def IsBinaryCoproduct.desc
    (h : IsBinaryCoproduct inl inr)
    {T : 𝓒}
    (f : X ⟶ T)
    (g : Y ⟶ T)
    : P ⟶ T :=
  IsColimit.desc h { pt := T, ι := mapPair f g }

@[simp]
theorem IsBinaryCoproduct.inl_desc
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    : inl ≫ h.desc f g = f :=
  h.fac { pt := T, ι := mapPair f g } (.mk .left)

@[simp]
theorem IsBinaryCoproduct.inr_desc
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    : inr ≫ h.desc f g = g :=
  h.fac { pt := T, ι := mapPair f g } (.mk .right)

theorem IsBinaryCoproduct.uniq
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    (m : P ⟶ T)
    (hf : inl ≫ m = f)
    (hg : inr ≫ m = g)
    : m = h.desc f g :=
  IsColimit.uniq h { pt := T, ι := mapPair f g } m fun
    | .mk .left => hf
    | .mk .right => hg

def IsBinaryCoproduct.map
    (fst : X ⟶ P)
    (snd : Y ⟶ P)
    {P' X' Y' : 𝓒}
    {fst' : X' ⟶ P'}
    {snd' : Y' ⟶ P'}
    (hg : IsBinaryCoproduct fst snd)
    (f : X ⟶ X')
    (g : Y ⟶ Y')
    : P ⟶ P' :=
  hg.desc (f ≫ fst') (g ≫ snd')

def IsBinaryCoproduct.hom_ext
    (h : IsBinaryCoproduct inl inr)
    {f g : P ⟶ T}
    (hl : inl ≫ f = inl ≫ g)
    (hr : inr ≫ f = inr ≫ g)
    : f = g :=
  BinaryCofan.IsColimit.hom_ext h hl hr

@[simp]
theorem IsBinaryCoproduct.inl_inr_desc
    (h : IsBinaryCoproduct inl inr)
    : h.desc inl inr = 𝟙 _ :=
  h.hom_ext
    ((h.inl_desc _ _).trans (Category.comp_id _).symm)
    ((h.inr_desc _ _).trans (Category.comp_id _).symm)

@[simp]
theorem IsBinaryCoproduct.desc_comp
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    (v : T ⟶ V)
    : h.desc f g ≫ v = h.desc (f ≫ v) (g ≫ v) :=
  h.hom_ext
    (by rw [← Category.assoc]; simp)
    (by rw [← Category.assoc]; simp)

def IsBinaryCoproduct.iso
    {X Y P₁ P₂ : 𝓒}
    {inl₁ : X ⟶ P₁} {inr₁ : Y ⟶ P₁}
    {inl₂ : X ⟶ P₂} {inr₂ : Y ⟶ P₂}
    (h₁ : IsBinaryCoproduct inl₁ inr₁)
    (h₂ : IsBinaryCoproduct inl₂ inr₂)
    : P₁ ≅ P₂ where
  hom := h₁.desc inl₂ inr₂
  inv := h₂.desc inl₁ inr₁
  hom_inv_id := hom_ext h₁ (by simp) (by simp)
  inv_hom_id := hom_ext h₂ (by simp) (by simp)

noncomputable def coproductIsBinaryCoproduct [cp : HasBinaryCoproduct X Y]
    : IsBinaryCoproduct (coprod.inl : X ⟶ X ⨿ Y) coprod.inr :=
  coprodIsCoprod X Y

noncomputable def coprod_homset_equiv
    [HasBinaryCoproduct X Y] {Z : 𝓒}
    : ((X ⨿ Y) ⟶ Z) ≃ ((X ⟶ Z) × (Y ⟶ Z)) where
  toFun   v := ⟨coprod.inl ≫ v, coprod.inr ≫ v⟩
  invFun  v := coprod.desc v.1 v.2
  left_inv a := by simp [←coprod.desc_comp]
  right_inv a := by simp

end coprod

end Limits

end CategoryTheory

