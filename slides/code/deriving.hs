data Fraction = Fraction Integer Integer
    deriving (Eq, Ord, Show)

data SortBy = Price | Size | Memory | CPUFrequency
    deriving (Enum)
