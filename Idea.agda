{-# OPTIONS --rewriting --without-K #-}

{-

To get Andrea Vezzosi's flat-ified Agda:

git clone https://github.com/agda/agda
cd agda
git checkout flat
cabal install --program-suffix=-flat

and then change your emacs startups to point to agda-flat and agda-mode-flat

-}

open import Agda.Primitive

module Idea where


  data _==_ {l1 : Level} {A : Set l1} (a : A) : A → Set l1 where
    refl : a == a

  postulate
    UNSAFE-PROMOTE : {l : Level} {A : Set l} → A → A

  postulate
    ♯'  : {l : Level} (A : Set l) → Set l

  ♯  : {l : Level} (A : Set l) → Set l
  ♯ A = ♯' (UNSAFE-PROMOTE A)

  postulate
    ♯i' : {l : Level} {A : Set l} → A → ♯ A

  ♯i : {l : Level} {A : Set l} → A → ♯ A
  ♯i A = ♯i' (UNSAFE-PROMOTE A)
  
  postulate
    ♯e : {l :{♭} Level} {A :{♭} Set l} → (x :{♭} (♯ A)) → A
    ♯β : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → (♯e (♯i x)) == x
    -- A and x wouldn't need to be ♭
    ♯η-crisp : {l :{♭} Level} {A :{♭} Set l} (x :{♭} ♯ A) → x == ♯i (♯e x)

  
