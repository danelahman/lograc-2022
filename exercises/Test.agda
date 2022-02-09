module Test where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

test : ℕ → ℕ
test n = n + 42
