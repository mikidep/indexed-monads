open import Prelude

open import Cubical.Foundations.Function using (idfun)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep)
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

  record _Π⇒_ (F G : IndexedContainer) {i : I} (s : F .S i) : Type where
    field
      σs : G .S i
      πs : ∀ {j} → G .P σs j → F .P s j

  open _Π⇒_ public

  module _ {F G : IndexedContainer} {i : I} {s : F .S i} where
    open import Cubical.Foundations.Isomorphism
    open Iso

    Π⇒IsoΣ : Iso ((F Π⇒ G) s) (Σ (G .S i) (λ σs → ∀ {j} → G .P σs j → F .P s j))
    Π⇒IsoΣ .fun x = x .σs , x .πs
    Π⇒IsoΣ .inv (σs , πs) = record { σs = σs ; πs = πs }
    Π⇒IsoΣ .rightInv _ = refl
    Π⇒IsoΣ .leftInv _ = refl

  module _ {F G : IndexedContainer} {i : I} {s : F .S i} {α β : (F Π⇒ G) s} where
    Π⇒PathP : 
      (≡σs : α .σs ≡ β .σs)
      (≡πs : PathP {ℓ-zero} (λ ι → ∀ {j} → G .P (≡σs ι) j → F .P s j) (α .πs) (β .πs))
      → α ≡ β
    Π⇒PathP ≡σs ≡πs ι .σs = ≡σs ι
    Π⇒PathP ≡σs ≡πs ι .πs = ≡πs ι

  _⇒_ : (F G : IndexedContainer) → Type
  F ⇒ G = (i : I) (s : F .S i) → (F Π⇒ G) s

  module _ {F G : IndexedContainer} {α β : F ⇒ G} where
    ⇒PathP :
      (Π≡ : {i : I} (s : F .S i) → α i s ≡ β i s)
      → α ≡ β
    ⇒PathP Π≡ ι i s = Π≡ s ι

  module _ {F G : IndexedContainer} {α β : F ⇒ G} (α≡β : α ≡ β) where
    σs≡ : {i : I} (s : F .S i) → α i s .σs ≡ β i s .σs
    σs≡ s ι = α≡β ι _ s .σs

    πs≡ : {i : I} (s : F .S i) {j : I}
      → PathP {ℓ-zero} (λ ι → G .P (σs≡ s ι) j → F .P s j) (α i s .πs) (β i s .πs)
    πs≡ s ι = α≡β ι _ s .πs

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
    _⟦$⟧_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ F ⟧ X i → ⟦ F ⟧ Y i)
    _⟦$⟧_ f i (s , v) = s , λ {j} p → f j (v p)

  module _ (F G : IndexedContainer) where
    _⊗_ : IndexedContainer
    _⊗_ .S = ⟦ G ⟧ (F .S) 
    _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

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

module _ {F G} (α : F ⇒ G) where
  record ⇒isIso : Type where
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

  unitor-l-inv-l : Path ((idᶜ ⊗ F) ⇒ (idᶜ ⊗ F)) (unitor-l ; unitor-l-inv) (id₁ (idᶜ ⊗ F))
  unitor-l-inv-l =
    ⇒PathP λ { (s , _) → Π⇒PathP
      (ΣPathP (refl , refl))
      ( implicitFunExt λ {j} →
        funExt λ { (k , p , k≡j) → ΣPathP
          ( sym k≡j
          , ΣPathP
            ( symP (subst-filler (P s) k≡j p)
            , symP λ ι κ → k≡j (ι ∨ κ)
            )
          )
        }
      )
    }

  unitor-r : (F ⊗ idᶜ) ⇒ F
  unitor-r _ (_ , si) .σs = si refl
  unitor-r i (_ , si) .πs p = i , refl , p

  unitor-r-inv : F ⇒ (F ⊗ idᶜ) 
  unitor-r-inv _ s .σs = _ , λ i≡j → subst S i≡j s
  unitor-r-inv i s .πs {j} (k , i≡k , p) = 
    transport P≡ p
    where
    P≡ : P {k} (subst S i≡k s) j ≡ P {i} s j
    P≡ = cong₂ (λ i s → P {i} s j) (sym i≡k) (symP (subst-filler S i≡k s))
    -- -- In a perfect world this would be:
    -- J
    --   (λ h i≡h → P (subst S i≡h s) j → P s j)
    --   (substP F (substRefl {B = S} s))
    --   i≡k
    --   p
    -- -- But this is not a perfect world.

module _ {F G H : IndexedContainer} where
  associator : (F ⊗ (G ⊗ H)) ⇒ ((F ⊗ G) ⊗ H)
  associator _ ((s″ , op″) , op′) .σs  = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator _ ((s″ , op″) , op′) .πs  (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

_² : IndexedContainer → IndexedContainer
IC ² = IC ⊗ IC


