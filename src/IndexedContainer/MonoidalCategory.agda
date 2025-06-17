open import Prelude
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv using (_≃_)


module IndexedContainer.MonoidalCategory {I : Type} where

open import IndexedContainer I 

module _ where
  open IndexedContainer

  idᶜ : IndexedContainer
  idᶜ .S _ = Unit
  idᶜ .P {i} _ j = i ≡ j

  -- It is useful to have this here
  module _ (X : I → Type) where
    open import Cubical.Foundations.Equiv
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma.Properties
    open import Cubical.Functions.Implicit

    idᶜ-≃ : ∀ i → ⟦ idᶜ ⟧ X i ≃ X i
    idᶜ-≃ i = 
      isoToEquiv lUnit×Iso 
      ∙ₑ implicit≃Explicit 
      ∙ₑ JEquiv _ _ _

  module _ (F G : IndexedContainer) where
    infixl 20 _⊗_

    _⊗_ : IndexedContainer
    _⊗_ .S = ⟦ G ⟧ (F .S) 
    _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

  module _ {F G H K : IndexedContainer} where
    infixl 21 _⊗₁_

    _⊗₁_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
    _⊗₁_ α β _ (Gs , Gsp→Fs) .fst = 
      let 
        Ks , Ksp→Gsp = β _ Gs
      in (Ks , λ Ksp → α _ (Gsp→Fs (Ksp→Gsp Ksp)) .fst) 
    _⊗₁_ α β _ (Gs , Gsp→Fs) .snd (k , Kp , Hp) = 
      let 
        Ks , Ksp→Gsp = β _ Gs
        Gsp = Ksp→Gsp Kp
      in k , Gsp , α _ (Gsp→Fs Gsp) .snd Hp

  module _ {F F′ : IndexedContainer} where
    ⊗₁-id : id₁ F ⊗₁ id₁ F′ ≡ id₁ (F ⊗ F′)
    ⊗₁-id = refl

  module _ {F F′ G G′ H H′ : IndexedContainer}
    (α  : F ⇒ G)   (β  : G ⇒ H)
    (α′ : F′ ⇒ G′) (β′ : G′ ⇒ H′)
    where
    ⊗₁-; : (α ; β) ⊗₁ (α′ ; β′) ≡ (α ⊗₁ α′) ; (β ⊗₁ β′)
    ⊗₁-; = refl

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

  unitor-l : F ⇒ idᶜ ⊗ F
  unitor-l i s = (s , _) , λ { (k , p , k≡j) → subst (P s) k≡j p }

  unitor-l-inv : idᶜ ⊗ F ⇒ F
  unitor-l-inv _ (s , _) = s , λ p → _ , p , refl

  unitor-l-inv-l : Path 
    (F ⇒ F) 
    (unitor-l ; unitor-l-inv)
    (id₁ F)
  unitor-l-inv-l ι i s = s , λ {j} p → transp (λ i₁ → P s j) ι p

  unitor-l-inv-r : Path 
    (idᶜ ⊗ F ⇒ idᶜ ⊗ F) 
    (unitor-l-inv ; unitor-l)
    (id₁ (idᶜ ⊗ F))
  unitor-l-inv-r =
    ⇒PathP λ { _ (s , _) → ΣPathP
      ( ΣPathP (refl , refl) 
      , implicitFunExt λ {j} →
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
  
  unitor-r : F ⊗ idᶜ ⇒ F
  unitor-r _ (_ , si) .fst = si refl
  unitor-r i (_ , si) .snd p = i , refl , p

  unitor-r-inv : F ⇒ F ⊗ idᶜ 
  unitor-r-inv _ s .fst = _ , λ i≡j → subst S i≡j s
  unitor-r-inv i s .snd {j} (k , i≡k , p) = 
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

  open IndexedContainer F 
  open IndexedContainer G renaming (S to S′; P to P′) 
  open IndexedContainer H renaming (S to S″; P to P″) 

  associator : F ⊗ (G ⊗ H) ⇒ (F ⊗ G) ⊗ H
  associator _ ((s″ , op″) , op′) .fst  = s″ , λ p″ → op″ p″ , λ p′ → op′ (_ , p″ , p′)
  associator _ ((s″ , op″) , op′) .snd (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

  associator-inv : (F ⊗ G) ⊗ H ⇒ F ⊗ (G ⊗ H)
  associator-inv _ (s″ , op) .fst .fst = (s″ , op » fst)
  associator-inv _ (s″ , op) .fst .snd (_ , p″ , p′) = op p″ .snd p′
  associator-inv _ (s″ , op) .snd (j , (k , p″ , p′) , p) = k , p″ , j , p′ , p

  is-inv-l : associator ; associator-inv ≡ id₁ _
  is-inv-l = refl

  is-inv-r : associator-inv ; associator ≡ id₁ _
  is-inv-r = refl

_² : IndexedContainer → IndexedContainer
IC ² = IC ⊗ IC
