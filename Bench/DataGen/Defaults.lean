-- import Batteries.Data.List.Basic

def List.product (l₁ : List α) (l₂ : List β) : List (α × β) := l₁.flatMap fun a => l₂.map (Prod.mk a)

infix:70 " ×' " => List.product
infix:71 " ×' " => List.product

-- def UNIQUE_RATIOS := [
--   0.1,
--   0.25,
--   0.5,
--   0.75,
--   0.9,
--   1,
-- ]

-- def SWAP_RATIOS := [
--   0,
--   0.001,
--   0.01,
--   0.05,
--   0.1,
--   0.5,
-- ]


-- def UNIQUE_RATIOS_WITH_DEFAULT_SWAPS := 0 :: UNIQUE_RATIOS.concat 1

-- def SIZES := [1000, 10000, 100000, 1000000]


def UNIQUE_RATIOS := [
  0,
  0.001,
  0.005,
  0.01,
  0.05,
  0.1,
  0.5,
]

-- #eval UNIQUE_RATIOS.map ( ( 1.0/· |>.toUInt64) )
def SWAP_RATIOS := [
  0,
  0.001,
  0.005,
  0.01,
  0.05,
  0.1,
  0.5,
]

-- #eval SWAP_RATIOS.map ( ( 1.0/· ) )

def UNIQUE_RATIOS_WITH_DEFAULT_SWAPS := UNIQUE_RATIOS -- .concat 1



def SPECIAL_PARAMS := ([false] ×' [1.0] ×' UNIQUE_RATIOS_WITH_DEFAULT_SWAPS)
def GENERAL_PARAMS := ([false, true] ×' SWAP_RATIOS ×' UNIQUE_RATIOS) ++ SPECIAL_PARAMS

#eval SPECIAL_PARAMS
#eval GENERAL_PARAMS.length

def SIZES := [
  1_000,
  5_000,
  10_000,
  50_000,
  100_000,

  500_000,
  1_000_000,

  -- 5_000_000
  -- 10_000_000
  -- 50_000_000
  -- 100_000_000
  -- 500_000_000
]
