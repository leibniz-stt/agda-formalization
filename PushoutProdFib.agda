{-# OPTIONS --cubical --guardedness --lossy-unification #-}
{-
This file contains a proof that fibres of pushout products commute
with joins (Rijke 2017, Theorem 2.2). Note that this proof is direct,
not relying on the flattening lemma (and in particular does not use
univalence).
-}
module PushoutProdFib where

-- Local imports
open import Prelude

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.PushoutProduct renaming (_×̂_ to _×^_)
open import Cubical.HITs.Join hiding (join) renaming (joinPushout to join)


open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    X : Type ℓ''
    Y : Type ℓ'''

------------
---------- Preservation under equivalence ----------
-- fibre commutes with join
module _ {f : A → B} {g : X → Y} where
  fib-×^→fib-join : (b : B) (y : Y)
    → fiber (f ×^ g) (b , y) → join (fiber f b) (fiber g y)
  fib-×^→fib-join b y = uncurry
    (elim∣inl (a , y') ↦ (λ p → inl (a , cong fst p))
         ∣inr (b' , x) ↦ (λ p → inr (x , cong snd p))
         ∣push (a , x)
           ↦ funExt λ p → push ((a , cong fst p) , (x , (cong snd p))))

  fib-join→fib-×^-push : (a : A) (x : X) (by : B × Y) (p : (f a , g x) ≡ by)
    → Path (fiber (f ×^ g) by)
            (inl (a , snd by) , ΣPathP (cong fst p , (λ _ → snd by)))
            (inr (fst by , x) , ΣPathP ((λ _ → fst by) , cong snd p))
  fib-join→fib-×^-push a x = J> cong₂ _,_ (push (a , x)) refl

  fib-join→fib-×^-pushβ : (a : A) (x : X)
    → fib-join→fib-×^-push a x _ refl ≡ cong₂ _,_ (push (a , x)) refl
  fib-join→fib-×^-pushβ a x = transportRefl _

  fib-join→fib-×^ : (b : B) (y : Y)
    → join (fiber f b) (fiber g y) → fiber (f ×^ g) (b , y)
  fib-join→fib-×^ b y =
    rec∣inl (a , p) ↦ (inl (a , y)) , ΣPathP (p , refl)
        ∣inr (x , p) ↦ inr (b , x) , ΣPathP (refl , p)
        ∣push ((a , p) , (x , q))
          ↦ fib-join→fib-×^-push a x (b , y) (ΣPathP (p , q))

  fib-×^→fib-join→fib-×^ : (b : B) (y : Y) (x : fiber (f ×^ g) (b , y))
    → fib-join→fib-×^ b y (fib-×^→fib-join b y x) ≡ x
  fib-×^→fib-join→fib-×^ b y = uncurry λ x →
    J (λ by p → fib-join→fib-×^ (fst by) (snd by)
                 (fib-×^→fib-join (fst by) (snd by) (x , p)) ≡ (x , p))
    (main x)
    where
    main : (x : _)
      → fib-join→fib-×^ (fst ((f ×^ g) x)) (snd ((f ×^ g) x))
         (fib-×^→fib-join (fst ((f ×^ g) x)) (snd ((f ×^ g) x)) (x , refl))
        ≡ (x , refl)
    main = elim∣inl (a , y') ↦ refl
               ∣inr (b' , x) ↦ refl
               ∣push (a , x) ↦ flipSquare (fib-join→fib-×^-pushβ a x)

  fib-join→fib-×^→fib-join : (b : B) (y : Y) (x : join (fiber f b) (fiber g y))
    → fib-×^→fib-join b y (fib-join→fib-×^ b y x) ≡ x
  fib-join→fib-×^→fib-join b y =
    elim∣inl (a , p) ↦ refl
        ∣inr (x , q) ↦ refl
        ∣push ((a , p) , (x , q))
          ↦ flipSquare (lem a x (b , y) (ΣPathP (p , q)))
    where
    lem : (a : A) (x : X) (by : B × Y) (p : (f a , g x) ≡ by)
      → cong (fib-×^→fib-join (fst by) (snd by))
               (cong (fib-join→fib-×^ (fst by) (snd by))
                (push ((a , cong fst p) , x , cong snd p)))
       ≡ push ((a , cong fst p) , (x , cong snd p))
    lem a x = J> cong (cong (fib-×^→fib-join (f a) (g x)))
                      (fib-join→fib-×^-pushβ a x)

  -- The main result
  Iso-Fib×-JoinFib : (b : B) (y : Y)
    → Iso (fiber (f ×^ g) (b , y)) (join (fiber f b) (fiber g y))
  Iso-Fib×-JoinFib b y .fun = fib-×^→fib-join b y
  Iso-Fib×-JoinFib b y .inv = fib-join→fib-×^ b y
  Iso-Fib×-JoinFib b y .sec = fib-join→fib-×^→fib-join b y
  Iso-Fib×-JoinFib b y .ret = fib-×^→fib-join→fib-×^ b y

  Fib×^≃JoinFib : (b : B) (y : Y)
    → fiber (f ×^ g) (b , y) ≃ join (fiber f b) (fiber g y)
  Fib×^≃JoinFib b y = isoToEquiv (Iso-Fib×-JoinFib b y)
