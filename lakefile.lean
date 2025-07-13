import Lake
open Lake DSL

package twin_primes where
  srcDir := "TwinPrimes"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0"
