{-# OPTIONS --cubical --guardedness --lossy-unification #-}

{-
This file contains a definition of orthogonality and proof of various
closure properties
-}

module LeibnizConstruction.Orthogonality where

-- Local imports
open import Prelude
open import Categories.ProtoWildCat
open import Categories.Map
open import LeibnizConstruction.Map

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open hasBiProtoFunctorStructure
open Iso


private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Type ℓ₁
    B : Type ℓ₂
    X : Type ℓ₃
    Y : Type ℓ₄

-- Definition of a diagonal map being a filler
record isFill (f : Map ℓ₁) (g : Map ℓ₂) (F : Map[ f , g ])
  (diag : Cod f → Dom g) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor isfill
  field
    triangL : diag ∘ (f ⃗) ≡ fst F
    triangR : (g ⃗) ∘ diag ≡ fst (snd F)
    sq : Square refl
                (funExt (snd (snd F))) (cong (_∘ (f ⃗)) triangR)
                (cong ((g ⃗) ∘_) triangL)

-- Definition of the type of diagonal fillers
Fill : (f : Map ℓ₁) (g : Map ℓ₂) (F : Map[ f , g ]) → Type _
Fill f g F = Σ[ diag ∈ (Cod f → Dom g) ] isFill f g F diag

-- Orthogonality
_⊥_ : (i : Map ℓ₁) (f : Map ℓ₂) → Type _
i ⊥ f = (ϕ : Map[ i , f ]) → isContr (Fill i f ϕ)

open isFill

-- i ⊥ f iff i ⋔ f is an equivalence
⊥↔isEquiv⋔ : (i : Map ℓ₁) (f : Map ℓ₂) → (i ⊥ f) ↔ isEquivMap (i ⋔ᵐ f)
⊥↔isEquiv⋔ (A , B , i) (X , Y , f) =
  (λ f → record { equiv-proof = λ b
    → isOfHLevelRetractFromIso 0 (invIso (lem' _)) (f _) })
  , λ isEq b → isOfHLevelRetractFromIso 0 (lem' _) (equiv-proof isEq _)
  where
  lem' : (ϕ : _) → Iso (Fill (A , B , i) (X , Y , f) ϕ)
                        (fiber (((A , B , i) ⋔ᵐ (X , Y , f)) ⃗)
                               ((ϕ .snd .fst) , (ϕ .fst) , funExt (snd (snd ϕ))))
  lem' (a , b , q) .fun F' =
    (F' .fst) , ΣPathP (triangR (F' .snd)
              , ΣPathP ((triangL (F' .snd))
              , sq (F' .snd)))
  lem' (a , b , q) .inv F' = _ , fl
    where
    fl : isFill (A , B , i) (X , Y , f) (a , b , q) (F' .fst)
    fl .triangL i a = F' .snd i .snd .fst a
    fl .triangR i a = F' .snd i .fst a
    fl .sq i j a = F' .snd i .snd .snd j a
  lem' (a , b , q) .sec _ = refl
  lem' (a , b , q) .ret _ = refl

-- identity maps are left and right orthogonal to all maps
module _ (A : Type ℓ₁) (g : Map ℓ₂) where
  private
    idMap⊥Fst : (ϕ : _) → Fill (idMap A) g ϕ
    idMap⊥Fst (a , b , q) .fst = a
    idMap⊥Fst (a , b , q) .snd .triangL = refl
    idMap⊥Fst (a , b , q) .snd .triangR i x = q x (~ i)
    idMap⊥Fst (a , b , q) .snd .sq i j x = q x (~ i ∨ j)


    ⊥idMapFst : (ϕ : _) → Fill g (idMap B) ϕ
    ⊥idMapFst (a , b , q) .fst = b
    ⊥idMapFst (a , b , q) .snd .triangL i x = q x i
    ⊥idMapFst (a , b , q) .snd .triangR = refl
    ⊥idMapFst (a , b , q) .snd .sq i j x = q x (i ∧ j)

  idMap⊥ : idMap A ⊥ g
  idMap⊥ M .fst = idMap⊥Fst M
  idMap⊥ (a , b , q) .snd (y , isfill triangL' triangR' sq') =
    lem a triangL' b triangR' (funExt q) sq'
    where
    -- rephrasing to apply J
    lem : (a : _) (triangL' : y ≡ a)
          (b : A → Cod g) (triangR' : (g ⃗) ∘ y ≡ b)
          (q : _) (sq' : Square refl q triangR' (cong ((g ⃗) ∘_) triangL'))
        → idMap⊥Fst (a , b , funExt⁻ q)
         ≡ (y , isfill triangL' triangR' sq')
    lem = J> (J> (J> refl))

  ⊥idMap : g ⊥ idMap A
  ⊥idMap M .fst = ⊥idMapFst M
  ⊥idMap (a , b , q) .snd (y , isfill triangL' triangR' sq') =
    lem a triangL' b triangR' (funExt q) sq'
    where
    -- rephrasing to apply J
    lem : (a : _) (triangL' : y ∘ (g ⃗) ≡ a)
          (b : _) (triangR' : y ≡ b)
          (q : _) (sq' : Square refl q (cong (_∘ (g ⃗)) triangR') triangL')
       → ⊥idMapFst (a , b , funExt⁻ q)
        ≡ (y , isfill triangL' triangR' sq')
    lem = J> (J> (J> refl))

-- equivalences are left and right orthogonal to all maps
module _ (e : Map ℓ₁) (g : Map ℓ₂) (eq : isEquivMap e) where
  private
    Equiv⊥×⊥Equiv : (e ⊥ g) × (g ⊥ e)
    Equiv⊥×⊥Equiv = main _ _ _ (_ , eq)
      where
      main : ∀ {ℓ₁ ℓ₂} (g : Map ℓ₂) (A B : Type ℓ₁) (e : A ≃ B)
        → ((A , B , fst e) ⊥ g) × (g ⊥ (A , B , fst e))
      main g A B e =
        EquivJ (λ A e → ((A , B , fst e) ⊥ g) × (g ⊥ (A , B , fst e)))
               (idMap⊥ _ g , ⊥idMap _ g) e

  ⊥Equiv : e ⊥ g
  ⊥Equiv = fst Equiv⊥×⊥Equiv

  Equiv⊥ : g ⊥ e
  Equiv⊥ = snd Equiv⊥×⊥Equiv

-- Leibniz products preserve left orthogonality 
⊠⊥ : (i j f : Map ℓ₁) → i ⊥ f → (i ⊠ᵐ j) ⊥ f
⊠⊥ i j f i⊥f =
  ⊥↔isEquiv⋔ (i ⊠ᵐ j) f .snd
     (subst isEquivMap j⋔[i⋔f]≡[i⊠j]⋔f
       (⊥↔isEquiv⋔ j (i ⋔ᵐ f) .fst (Equiv⊥ _ j isEquiv-i⋔f)))
  where
  isEquiv-i⋔f : isEquivMap (i ⋔ᵐ f)
  isEquiv-i⋔f = ⊥↔isEquiv⋔ i f .fst i⊥f

  j⋔[i⋔f]≡[i⊠j]⋔f : j ⋔ᵐ (i ⋔ᵐ f) ≡ (i ⊠ᵐ j) ⋔ᵐ f
  j⋔[i⋔f]≡[i⊠j]⋔f = sym (Iso-[[⊠ᵐ]-⋔ᵐ]-[⋔ᵐ-[⋔ᵐ]] j i f)
                  ∙ cong (_⋔ᵐ f) (invEq univalenceMap (comm⊠ᵐ _ _))

-- ⊥ is closed under retracts
retract⊥ : (i j f : Map ℓ₁) → retractMap j i → i ⊥ f → j ⊥ f
retract⊥ i j f (j→i , i→j , c) i⊥f = ⊥↔isEquiv⋔ j f .snd
  (retrEquivMap (i ⋔ᵐ f) (j ⋔ᵐ f) isEquiv-i⋔f closedRetract)
  where
  isEquiv-i⋔f : isEquivMap (i ⋔ᵐ f)
  isEquiv-i⋔f = ⊥↔isEquiv⋔ i f .fst i⊥f

  closedRetract : retractMap (j ⋔ᵐ f) (i ⋔ᵐ f)
  closedRetract .fst = ⋔ᵐ→ₗ i j f i→j
  closedRetract .snd .fst = ⋔ᵐ→ₗ j i f j→i
  closedRetract .snd .snd =
    sym (leftAct (hasBiProtoFunctorStructure⋔ᵐ) f .snd .snd i→j j→i)
    ∙ cong (leftAct hasBiProtoFunctorStructure⋔ᵐ f .fst) c
    ∙ leftAct (hasBiProtoFunctorStructure⋔ᵐ) f .snd .fst j
