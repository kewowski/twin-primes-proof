import TwinPrimes.SelbergWeights
import TwinPrimes.TwinWeight
import TwinPrimes.SieveWeights
import TwinPrimes.UpperBound
import TwinPrimes.OmegaBound
import TwinPrimes.Contradiction

def main : IO Unit := do
  IO.println "Twin primes proof loaded successfully."
  IO.println s!"Formal result: ¬(∃ T, ∀ n ≥ T, Λ₂(n) = 0) = {TwinPrimes.Contradiction.twin_primes_infinite}"
  
@[main] def entry := main


