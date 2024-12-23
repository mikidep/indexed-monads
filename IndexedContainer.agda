open import Prelude

open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep; funExtNonDep; funExtNonDep⁻)
open import Cubical.Data.Unit

module IndexedContainer (I : Type) where

record IndexedContainer  : Type₁ where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  substP : (F : IndexedContainer) {i : I} {s s′ : F .S i} {j : I} (s≡s′ : s ≡ s′)  
    → F .P s j → F .P s′ j
  substP F {j = j} = subst (λ s → F .P s j)

  record _⇒_ (F G : IndexedContainer) : Type₁ where
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

    ⇒PathP-extP :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} → PathP (λ ι → G .P (≡σ s ι) j → F .P s j) (α .π s) (β .π s))
      → α ≡ β
    ⇒PathP-extP ≡σ ≡π = ⇒PathP
      (implicitFunExt λ {i} → funExt ≡σ)
      (implicitFunExt λ {i} → funExt λ s → implicitFunExt λ {j} → ≡π s)

    ⇒PathP-extΣ :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} → PathP (λ ι → G .P (≡σ s ι) j → F .P s j) (α .π s) (β .π s))
      → α ≡ β
    ⇒PathP-extΣ ≡σ ≡π = ⇒PathP
      (implicitFunExt λ {i} → funExt ≡σ)
      (implicitFunExt λ {i} → funExt λ s → implicitFunExt λ {j} → ≡π s)

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
      (≡π : ∀ {i} (s : F .S i) {j} (p : G .P (α .σ s) j) → α .π s p ≡ β .π s (substP G (≡σ s) p))
      → α ≡ β
    ⇒PathP-ext′ ≡σ ≡π =
      ⇒PathP-ext″ ≡σ
        λ s {j} → funExt⁻ $
          let
            ≡π-ext⁻ : α .π s ≡ substP G (≡σ s) » β .π s
            ≡π-ext⁻ = funExt $ ≡π s {j}
          in cong (subst (λ s′ → P G s′ j → F .P s j) (≡σ s)) ≡π-ext⁻ ∙ substDomain (λ s′ → P G s′ j) (≡σ s) (β .π s {j})

    σ≡ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) → α .σ s ≡ β .σ s
    σ≡ α≡β s = cong (λ γ → γ .σ s) α≡β

    substPσ : ∀ (α≡β : α ≡ β) {i} {s : F .S i} {j} → G .P (α .σ s) j → G .P (β .σ s) j
    substPσ α≡β {s} = substP G (σ≡ α≡β s)

    π≡ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) {j} (p : G .P _ j)
      → α .π s p ≡ β .π s (substPσ α≡β p)
    π≡ α≡β s p = (funExtNonDep⁻ $ cong (λ γ → γ .π s) α≡β) (toPathP refl)
      where
      open import Cubical.Functions.FunExtEquiv using (funExtNonDep⁻)

  record _Π⇒_ (F G : IndexedContainer) {i : I} (s : F .S i) : Type₁ where
    field
      σs : G .S i
      πs : ∀ {j} → G .P σs j → F .P s j

  open _Π⇒_ public

  module _ {F G : IndexedContainer} {i : I} {s : F .S i} {α β : (F Π⇒ G) s} where
    Π⇒PathP : 
      (≡σs : α .σs ≡ β .σs)
      (≡πs : PathP {ℓ-zero} (λ ι → ∀ {j} → G .P (≡σs ι) j → F .P s j) (λ {j} → α .πs {j}) (β .πs))
      → α ≡ β
    Π⇒PathP ≡σs ≡πs ι .σs = ≡σs ι
    Π⇒PathP ≡σs ≡πs ι .πs = ≡πs ι

  _⇒′_ : (F G : IndexedContainer) → Type₁
  F ⇒′ G = {i : I} (s : F .S i) → (F Π⇒ G) s

  module _ {F G : IndexedContainer} {α β : F ⇒′ G} where
    ⇒′PathP :
      (Π≡ : {i : I} (s : F .S i) → α s ≡ β s)
      → (λ {i} → α {i}) ≡ β
    ⇒′PathP Π≡ ι s = Π≡ s ι

--   idᶜ : IndexedContainer
--   idᶜ .S _ = Unit
--   idᶜ .P {i} _ j = i ≡ j
--
--   module _ (F) where
--     id₁ : F ⇒ F 
--     id₁ .σ s = s
--     id₁ .π s p = p
--
--   module _ (F : IndexedContainer) where
--     ⟦_⟧ : (I → Type) → (I → Type)
--     ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ {j} (p : F .P s j) → X j)
--
--     _⟨$⟩_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦_⟧ X i → ⟦_⟧ Y i)
--     _⟨$⟩_ f i (s , v) .fst = s
--     _⟨$⟩_ f i (s , v) .snd {j} p = f j (v p)
--
--   module _ (F G : IndexedContainer) where
--     _⊗_ : IndexedContainer
--     _⊗_ .S = ⟦ G ⟧ (F .S) 
--     _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k
--
--   -- interpretation is strong monoidal
--   module _ (X : I → Type) where
--     open import Cubical.Foundations.Equiv using (_≃_)
--
--     idᶜ-≃ : ∀ i → ⟦ idᶜ ⟧ X i ≃ X i
--     idᶜ-≃ i = isoToEquiv idᶜ-iso
--       where
--       open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
--       open Iso
--       idᶜ-iso : Iso (⟦ idᶜ ⟧ X i) (X i)
--       idᶜ-iso .fun (_ , x) = x refl
--       idᶜ-iso .inv x = _ , λ i≡j → subst X i≡j x
--       idᶜ-iso .rightInv x = transportRefl x
--       idᶜ-iso .leftInv (_ , x) = ΣPathP
--         ( refl
--         , implicitFunExt λ {j} → funExt λ i≡j
--           → J (λ k i≡k → subst X i≡k (x refl) ≡ x i≡k) (substRefl {B = X} (x refl)) i≡j
--         )
--         where
--           open import Cubical.Data.Sigma using (ΣPathP)
--
--     ⊗-≃ : ∀ F G i → (⟦ F ⟧ » ⟦ G ⟧) X i ≃ ⟦ F ⊗ G ⟧ X i
--     ⊗-≃ F G i = isoToEquiv ⊗-iso where
--       open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
--       open Iso
--       ⊗-iso : Iso ((⟦ F ⟧ » ⟦ G ⟧) X i) (⟦ F ⊗ G ⟧ X i)
--       ⊗-iso .fun (s , v) = (s , λ p → v p .fst) , λ { (k , p , q) → v p .snd q }
--       ⊗-iso .inv ((s , v) , w) = s , λ p → v p , λ q → w (_ , p , q)
--       ⊗-iso .rightInv _ = refl
--       ⊗-iso .leftInv  _ = refl
--
-- module _ {F G H K} where
--   _⊗₁_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
--   (α ⊗₁ β) .σ (Gs , Gsp→Fs) = β .σ Gs , λ { {j} Ksp → α .σ (Gsp→Fs (β .π Gs Ksp)) }
--   (α ⊗₁ β) .π {i} (Gs , Gsp→Fs) (i′ , Kp , Hp) = let
--       Gsp = β .π Gs Kp 
--     in i′ , Gsp , α .π (Gsp→Fs Gsp) Hp
--
-- module _ {F G H} where
--   _;_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
--   (α ; β) .σ s = β .σ (α .σ s)
--   (α ; β) .π s p = α .π s (β .π (α .σ s) p)
--
-- -- module _ {F G} where
-- --   id₁-⊗ₕ : id₁ {F} ⊗ₕ id₁ {G} ≡ id₁ {F ⊗ G}
-- --   id₁-⊗ₕ = ⇒PathP-ext′
-- --     (λ { s → refl })
-- --     (λ { s p → sym $ substRefl p })
-- --
--
-- module _ {F G} (α : F ⇒ G) where
--   record ⇒isIso : Type₁ where
--     field
--       inv : G ⇒ F
--       inv-l : α ; inv ≡ id₁ F
--       inv-r : inv ; α ≡ id₁ G
--
-- module _ {F} where
--   open import Cubical.Data.Sigma using (ΣPathP)
--   open import Cubical.Foundations.Path using (toPathP⁻; fromPathP⁻)
--
--   open IndexedContainer F
--   open ⇒isIso
--
--   unitor-l : (idᶜ ⊗ F) ⇒ F
--   unitor-l .σ (s , _) = s
--   unitor-l .π {i} (s , _) {j} p = j , p , refl
--
--   unitor-l-inv : F ⇒ (idᶜ ⊗ F)
--   unitor-l-inv .σ s = s , _
--   unitor-l-inv .π s (k , p , k≡j) = subst (P s) k≡j p
--
--   unitor-l-iso : ⇒isIso unitor-l
--   unitor-l-iso .inv = unitor-l-inv
--   unitor-l-iso .inv-l = ⇒PathP-extP
--     (λ _ → refl)
--     λ _ {j} → funExt λ { 
--       (k , p , k≡j) → ΣPathP
--       ( sym k≡j
--       , ΣPathP
--         ( toPathP⁻ refl
--         , toPathP⁻
--           ( J
--             (λ h j≡h → refl ≡ subst (_≡ j) (sym j≡h) (sym j≡h))
--             (sym (substRefl {B = _≡ j} refl))
--             (sym k≡j)
--           )
--         )
--       )
--     } 
--   unitor-l-iso .inv-r = ⇒PathP-extP
--     (λ _ → refl )
--     λ s {j} → funExt (substRefl {B = P s}) 
--
--   unitor-r : (F ⊗ idᶜ) ⇒ F
--   unitor-r .σ (_ , si) = si refl
--   unitor-r .π {i} (_ , si) p = i , refl , p
--
--   unitor-r-inv : F ⇒ (F ⊗ idᶜ) 
--   unitor-r-inv .σ s = _ , λ {_} i≡j → subst S i≡j s
--   unitor-r-inv .π s {j} (k , i≡k , p) = J
--     (λ h i≡h → P (subst S i≡h s) j → P s j)
--     (substP F (substRefl {B = S} s))
--     i≡k
--     p
--
--   unitor-r-iso : ⇒isIso unitor-r
--   unitor-r-iso .inv = unitor-r-inv
--   unitor-r-iso .inv-l = ⇒PathP-extP
--     (λ { {i} (_ , si) → 
--       ΣPathP
--         ( refl
--         , implicitFunExt
--           λ {j} → funExt 
--             λ i≡j → J
--               (λ h i≡h → subst S i≡h (si (λ _ → i)) ≡ si i≡h)
--               (substRefl {B = S} (si refl))
--               i≡j
--         )
--     })
--     λ { {i} (_ , si) {j} → funExtNonDep {! !} 
--
--     }
--   unitor-r-iso .inv-r = {! !}
--
-- module _ {F G H} where
--   associator : (F ⊗ (G ⊗ H)) ⇒ ((F ⊗ G) ⊗ H)
--   associator .σ ((s″ , op″) , op′) = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
--   associator .π ((s″ , op″) , op′) (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p
--
-- _² : IndexedContainer → IndexedContainer
-- IC ² = IC ⊗ IC
--
