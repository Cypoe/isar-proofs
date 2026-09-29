import ISAR.SpecVocabulary
namespace ISAR

-- increment 0x00000000 -> 0x00000001: bytes [(0,0),(0,0),(0,0),(0,0)]
-- byteLit lo hi; LE order: b0 least significant
#eval hsteps 400 (aps b4incL [b4Lit [(0,0),(0,0),(0,0),(0,0)]])
