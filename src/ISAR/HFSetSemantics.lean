import ISAR.HFSetEncoding

namespace ISAR

noncomputable def InvariantLayer.empty : InvariantLayer :=
  HF_encode HF.empty

noncomputable def InvariantLayer.pair (x y : InvariantLayer) : InvariantLayer :=
  HF_encode (HF.pair (decode_layer x) (decode_layer y))

noncomputable def InvariantLayer.union (x y : InvariantLayer) : InvariantLayer :=
  HF_encode (HF.union (decode_layer x) (decode_layer y))

theorem HF_encode_empty : HF_encode HF.empty = InvariantLayer.empty := rfl

theorem HF_encode_pair (x y : HF) :
    HF_encode (HF.pair x y) = InvariantLayer.pair (HF_encode x) (HF_encode y) := by
  unfold InvariantLayer.pair
  rw [decode_layer_HF_encode, decode_layer_HF_encode]

theorem HF_encode_union (x y : HF) :
    HF_encode (HF.union x y) = InvariantLayer.union (HF_encode x) (HF_encode y) := by
  unfold InvariantLayer.union
  rw [decode_layer_HF_encode, decode_layer_HF_encode]

end ISAR
