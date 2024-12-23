open import Prelude

open import Cubical.Foundations.Function using (idfun)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep; funExtNonDep; funExtNonDep⁻)
open import Cubical.Data.Unit

module IndexedContainerSigma (I : Type) where

record IndexedContainer  : Type₁ where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  substP : (F : IndexedContainer) {i : I} {s s′ : F .S i} {j : I} (s≡s′ : s ≡ s′)  
    → F .P s j → F .P s′ j
  substP F {j = j} = subst (λ s → F .P s j)

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

  _⇒_ : (F G : IndexedContainer) → Type₁
  F ⇒ G = (i : I) (s : F .S i) → (F Π⇒ G) s

  module _ {F G : IndexedContainer} {α β : F ⇒ G} where
    ⇒PathP :
      (Π≡ : {i : I} (s : F .S i) → α i s ≡ β i s)
      → α ≡ β
    ⇒PathP Π≡ ι i s = Π≡ s ι

  idᶜ : IndexedContainer
  idᶜ .S _ = Unit
  idᶜ .P {i} _ j = i ≡ j

  module _ (F : IndexedContainer) where
    id₁ : F ⇒ F 
    id₁ _ s .σs = s
    id₁ _ s .πs = idfun _

  module _ (F : IndexedContainer) where
    ⟦_⟧ : (I → Type) → (I → Type)
    ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ {j} (p : F .P s j) → X j)

  module _ (F : IndexedContainer) where
    _⟨$⟩_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ F ⟧ X i → ⟦ F ⟧ Y i)
    _⟨$⟩_ f i (s , v) .fst = s
    _⟨$⟩_ f i (s , v) .snd {j} p = f j (v p)

  module _ (F G : IndexedContainer) where
    _⊗_ : IndexedContainer
    _⊗_ .S = ⟦ G ⟧ (F .S) 
    _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

  -- interpretation is strong monoidal
  module _ (X : I → Type) where
    open import Cubical.Foundations.Equiv using (_≃_)

    idᶜ-≃ : ∀ i → ⟦ idᶜ ⟧ X i ≃ X i
    idᶜ-≃ i = isoToEquiv idᶜ-iso
      where
      open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
      open Iso
      idᶜ-iso : Iso (⟦ idᶜ ⟧ X i) (X i)
      idᶜ-iso .fun (_ , x) = x refl
      idᶜ-iso .inv x = _ , λ i≡j → subst X i≡j x
      idᶜ-iso .rightInv x = transportRefl x
      idᶜ-iso .leftInv (_ , x) = ΣPathP
        ( refl
        , implicitFunExt λ {j} → funExt λ i≡j
          → J (λ k i≡k → subst X i≡k (x refl) ≡ x i≡k) (substRefl {B = X} (x refl)) i≡j
        )
        where
          open import Cubical.Data.Sigma using (ΣPathP)

    ⊗-≃ : ∀ F G i → (⟦ F ⟧ » ⟦ G ⟧) X i ≃ ⟦ F ⊗ G ⟧ X i
    ⊗-≃ F G i = isoToEquiv ⊗-iso where
      open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
      open Iso
      ⊗-iso : Iso ((⟦ F ⟧ » ⟦ G ⟧) X i) (⟦ F ⊗ G ⟧ X i)
      ⊗-iso .fun (s , v) = (s , λ p → v p .fst) , λ { (k , p , q) → v p .snd q }
      ⊗-iso .inv ((s , v) , w) = s , λ p → v p , λ q → w (_ , p , q)
      ⊗-iso .rightInv _ = refl
      ⊗-iso .leftInv  _ = refl

-- module _ {F G H K} where
--   _⊗₁_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
--   (α ⊗₁ β) .σ (Gs , Gsp→Fs) = β .σ Gs , λ { {j} Ksp → α .σ (Gsp→Fs (β .π Gs Ksp)) }
--   (α ⊗₁ β) .π {i} (Gs , Gsp→Fs) (i′ , Kp , Hp) = let
--       Gsp = β .π Gs Kp 
--     in i′ , Gsp , α .π (Gsp→Fs Gsp) Hp

module _ {F G H K : IndexedContainer} where
  _⊗₁_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
  (α ⊗₁ β) _ (Gs , Gsp→Fs) .σs = β _ Gs .σs , λ p → α _ (Gsp→Fs (β _ Gs .πs p)) .σs 
  (α ⊗₁ β) _ (Gs , Gsp→Fs) .πs (k , Kp , Hp) = let
      Gsp = β _ Gs .πs Kp
    in k , Gsp , α _ (Gsp→Fs Gsp) .πs Hp

module _ {F G H : IndexedContainer} where
  infixl 20 _;_
  _;_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ; β) _ s .σs   = β _ (α _ s .σs) .σs 
  (α ; β) _ s .πs p = α _ s .πs (β _ (α _ s .σs) .πs p)

-- module _ {F G} where
--   id₁-⊗ₕ : id₁ {F} ⊗ₕ id₁ {G} ≡ id₁ {F ⊗ G}
--   id₁-⊗ₕ = ⇒PathP-ext′
--     (λ { s → refl })
--     (λ { s p → sym $ substRefl p })


module _ {F G} (α : F ⇒ G) where
  record ⇒isIso : Type₁ where
    field
      inv : G ⇒ F
      inv-l : Path (F ⇒ F) (α ; inv) (id₁ F)
      inv-r : Path (G ⇒ G) (inv ; α) (id₁ G)

module _ {F : IndexedContainer} where
  open import Cubical.Foundations.Path using (toPathP⁻; fromPathP⁻)
  open import Cubical.Data.Sigma using (ΣPathP)

  open IndexedContainer F
  open ⇒isIso

  unitor-l : (idᶜ ⊗ F) ⇒ F
  unitor-l _ (s , _) .σs = s
  unitor-l i (s , _) .πs {j} p = j , p , refl

  unitor-l-inv : F ⇒ (idᶜ ⊗ F)
  unitor-l-inv _ s .σs = s , _
  unitor-l-inv _ s .πs (k , p , k≡j) = subst (P s) k≡j p

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

  
  unitor-l-inv-l : Path ((idᶜ ⊗ F) ⇒ (idᶜ ⊗ F)) (unitor-l ; unitor-l-inv) (id₁ (idᶜ ⊗ F))
  unitor-l-inv-l =
    ⇒PathP λ { (s , _) → Π⇒PathP
      (ΣPathP (refl , refl))
      ( implicitFunExt λ {j} →
        funExt λ { (k , p , k≡j) → ΣPathP
          ( sym k≡j
          , ΣPathP
            ( toPathP⁻ refl
            , toPathP⁻
              ( J
                (λ h j≡h → refl ≡ subst (_≡ j) (sym j≡h) (sym j≡h))
                (sym (substRefl {B = _≡ j} refl))
                (sym k≡j)
              )
            )
          )
        }
      )
    }

  unitor-r : (F ⊗ idᶜ) ⇒ F
  unitor-r _ (_ , si) .σs = si refl
  unitor-r i (_ , si) .πs p = i , refl , p

  unitor-r-inv : F ⇒ (F ⊗ idᶜ) 
  unitor-r-inv _ s .σs = _ , λ {_} i≡j → subst S i≡j s
  unitor-r-inv _ s .πs {j} (k , i≡k , p) = J
    (λ h i≡h → P (subst S i≡h s) j → P s j)
    (substP F (substRefl {B = S} s))
    i≡k
    p

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

module _ {F G H : IndexedContainer} where
  associator : (F ⊗ (G ⊗ H)) ⇒ ((F ⊗ G) ⊗ H)
  associator _ ((s″ , op″) , op′) .σs  = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator _ ((s″ , op″) , op′) .πs  (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

_² : IndexedContainer → IndexedContainer
IC ² = IC ⊗ IC

