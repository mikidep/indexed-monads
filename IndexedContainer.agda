open import Prelude

open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep; funExtNonDep; funExtNonDep⁻)
open import Cubical.Data.Unit

module IndexedContainer (I : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  record _⇒_ (F G : IndexedContainer) : Type (ℓ-suc ℓ-zero) where
    field
      σ : ∀ {i} → F .S i → G .S i
      π : ∀ {i} (s : F .S i) {j} → G .P (σ s) j → F .P s j

  open _⇒_ public

  module _ {F G : IndexedContainer} {α β : F ⇒ G} where
    ⇒PathP :
      (≡σ : (λ {i} → α .σ {i}) ≡ β .σ)
      (≡π : PathP {ℓ-zero} (λ ι → ∀ {i} (s : F .S i) {j} → G .P (≡σ ι s) j → F .P s j) (λ {i} → α .π {i}) (β .π))
      → α ≡ β
    ⇒PathP ≡σ ≡π 𝒾 .σ = ≡σ 𝒾
    ⇒PathP ≡σ ≡π 𝒾 .π = ≡π 𝒾

    ⇒PathP-ext :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ (i : I) (s : F .S i) j
        → {p₁ : G .P (α .σ s) j} {p₂ : G .P (β .σ s) j}
          (p≡ : p₁ ≡[ ≡σ s , (λ s′ → G .P s′ j) ] p₂)
        → (α .π s p₁) ≡ (β .π s p₂))
      → α ≡ β
    ⇒PathP-ext ≡σ ≡π = ⇒PathP
      (implicitFunExt λ {i} → funExt ≡σ)
      (implicitFunExt λ {i} → funExt λ s → implicitFunExt λ {j} → funExtNonDep (≡π i s j))

    substDomain : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {x y : A}
      (B : A → Type ℓ′) {C : Type ℓ″}
      (x≡y : x ≡ y)
      (f : B y → C)
      → subst (λ a → B a → C) x≡y (subst B x≡y » f) ≡ f
    substDomain {A} {x} {y} B {C} =
      J
        (λ z x≡z → (f : B z → C) → subst (λ a → B a → C) x≡z (subst B x≡z » f) ≡ f)
        goal
      where module _ (f : B x → C) where
        B→C = λ a → B a → C

        aux : subst B refl » f ≡ f
        aux = funExt λ x → cong f (substRefl {B = B} x)

        goal : subst B→C refl (subst B refl » f) ≡ f 
        goal = substRefl {B = B→C} (subst B refl » f) ∙ aux

    ⇒PathP-ext″ :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} (p : G .P (β .σ s) j) → subst (λ s′ → G .P s′ j → F .P s j) (≡σ s) (α .π s) p ≡ β .π s p)
      → α ≡ β
    ⇒PathP-ext″ ≡σ ≡π = ⇒PathP
        (implicitFunExt λ {i} → funExt ≡σ)
        (implicitFunExt
          λ {i} → funExt
            λ s → implicitFunExt
              λ {j} → toPathP (funExt (≡π s))
        )

    ⇒PathP-ext′ :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} (p : G .P (α .σ s) j) → α .π s p ≡ β .π s (subst (λ s′ → G .P s′ j) (≡σ s) p))
      → α ≡ β
    ⇒PathP-ext′ ≡σ ≡π =
      ⇒PathP-ext″ ≡σ
        λ s {j} → funExt⁻ $
          let
            ≡π-ext⁻ : α .π s ≡ subst (λ s′ → P G s′ j) (≡σ s) » β .π s
            ≡π-ext⁻ = funExt $ ≡π s {j}
          in cong (subst (λ s′ → P G s′ j → P F s j) (≡σ s)) ≡π-ext⁻ ∙ substDomain (λ s′ → P G s′ j) (≡σ s) (β .π s {j})

    σ≡ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) → α .σ s ≡ β .σ s
    σ≡ α≡β s = cong (λ γ → γ .σ s) α≡β

    substP : ∀ (α≡β : α ≡ β) {i} {s : F .S i} {j} → G .P (α .σ s) j → G .P (β .σ s) j
    substP α≡β {i} {s} {j} = subst (λ s′ → G .P s′ j) (σ≡ α≡β s)

    π≡ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) {j} (p : G .P _ j)
      → α .π s p ≡ β .π s (substP α≡β p)
    π≡ α≡β s p = (funExtNonDep⁻ $ cong (λ γ → γ .π s) α≡β) (toPathP refl)
      where
      open import Cubical.Functions.FunExtEquiv using (funExtNonDep⁻)

    -- π≡′ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) {j} (p : G .P (β .σ s) j)
    --   → subst (λ s′ → G .P s′ j → F .P s j) (σ≡ α≡β s) (α .π s) p ≡ β .π s p
    -- π≡′ α≡β s {j} =
    --   let
    --     πeq : ∀ {i} (s : F .S i) {j : I} → PathP (λ ι → G .P (σ≡ α≡β s ι) j → F .P s j) (α .π s) (β .π s) 
    --     πeq s ι = α≡β ι .π s  
    --   in {! !}
    
  idᶜ : IndexedContainer
  idᶜ .S _ = Unit
  idᶜ .P {i} _ j = i ≡ j

  module _ {F} where
    id₁ : F ⇒ F 
    id₁ .σ s = s
    id₁ .π s p = p

  module _ (F : IndexedContainer) where
    ⟦_⟧ : (I → Type) → (I → Type)
    ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ {j} (p : F .P s j) → X j)

    _⟨$⟩_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦_⟧ X i → ⟦_⟧ Y i)
    _⟨$⟩_ f i (s , v) .fst = s
    _⟨$⟩_ f i (s , v) .snd {j} p = f j (v p)

  module _ (F G : IndexedContainer) where
    _⊗_ : IndexedContainer
    _⊗_ .S = ⟦ G ⟧ (F .S) 
    _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

    -- interpretation is strong monoidal
    -- module _ (X : I → Type) (i : I) where
    --   ⊗-≃ : ∀ i → ⟦ G ⟧ (⟦ F ⟧ X) i ≃ ⟦ _⊗_ ⟧ X i
    --   ⊗-≃ i = isoToEquiv ⊗-iso where
    --     open Iso
    --     ⊗-iso : Iso (⟦ G ⟧ (⟦ F ⟧ X) i) (⟦ _⊗_ ⟧ X i)
    --     -- ⊗-iso .fun (s′ , br) = (s′ , λ j p → br j p .fst) , λ { k (j , (p′ , p)) → br j p′ .snd k p }
    --     ⊗-iso .fun (s′ , br) = {! !}
    --     -- ⊗-iso .inv ((s′ , br) , ⊗ops) = s′ , λ { j p′ → br j p′ , λ { k p → ⊗ops k (j , p′ , p) } }
    --     ⊗-iso .inv ((s′ , br) , ⊗ops) = {! !}
    --     ⊗-iso .rightInv _ = refl
    --     ⊗-iso .leftInv _ = refl

module _ {F G H K} where
  _⊗ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
  (α ⊗ₕ β) .σ (Gs , Gsp→Fs) = β .σ Gs , λ { {j} Ksp → α .σ (Gsp→Fs (β .π Gs Ksp)) }
  (α ⊗ₕ β) .π {i} (Gs , Gsp→Fs) (i′ , Kp , Hp) = let
      Gsp = β .π Gs Kp 
    in i′ , Gsp , α .π (Gsp→Fs Gsp) Hp

module _ {F G H} where
  _⊗ᵥ_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ⊗ᵥ β) .σ s = β .σ (α .σ s)
  (α ⊗ᵥ β) .π s p = α .π s (β .π (α .σ s) p)

-- module _ {F G} where
--   id₁-⊗ₕ : id₁ {F} ⊗ₕ id₁ {G} ≡ id₁ {F ⊗ G}
--   id₁-⊗ₕ = ⇒PathP-ext′
--     (λ { s → refl })
--     (λ { s p → sym $ substRefl p })
--
-- -- module _ {F G} (α : F ⇒ G) where
--   record ⇒Iso : Type ℓ-zero where
--     field
--       inv : G ⇒ F
--       inv-l : α ⊗ᵥ inv ≡ id₁
--       inv-r : inv ⊗ᵥ α ≡ id₁
--
module _ {F} where

  open IndexedContainer F

  -- open ⇒Iso

  unitor-l : (idᶜ ⊗ F) ⇒ F
  unitor-l .σ (s , _) = s
  unitor-l .π {i} (s , _) {j} p = j , p , refl

  -- unitor-l-inv : F ⇒ (idᶜ ⊗ F)
  -- unitor-l-inv .σ s = s , _
  -- unitor-l-inv .π s (k , p , k≡j) = subst (P s) k≡j p
  --
  -- unitor-l-iso : ⇒Iso unitor-l
  -- unitor-l-iso .inv = unitor-l-inv
  -- unitor-l-iso .inv-l = ⇒PathP-ext′
  --   (λ { s → refl })
  --   λ { s p → sym $ substRefl p }
  -- unitor-l-iso .inv-r = {! !}


  unitor-r : (F ⊗ idᶜ) ⇒ F
  unitor-r .σ (_ , si) = si refl
  unitor-r .π {i} (_ , si) p = i , refl , p

module _ {F G H} where
  associator : (F ⊗ (G ⊗ H)) ⇒ ((F ⊗ G) ⊗ H)
  associator .σ ((s″ , op″) , op′) = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator .π ((s″ , op″) , op′) (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

_² : IndexedContainer → IndexedContainer
IC ² = IC ⊗ IC

