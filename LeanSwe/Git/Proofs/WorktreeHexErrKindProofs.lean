import LeanSwe.Git.Impl

set_option Elab.async false

namespace LeanSwe.Git.Proofs

private theorem decodeUtf8Lossy_toUTF8_local (s : String) :
    Impl.decodeUtf8Lossy s.toUTF8 = s := by
  unfold Impl.decodeUtf8Lossy
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]

private theorem err5_trim_empty :
    (Impl.trimAsciiWhitespace "fatal: cannot update HEAD").isEmpty = false := by
  cbv

private theorem err5_san :
    Impl.sanitizeLowerForClassify "fatal: cannot update HEAD" = "fatal: cannot update head".toList := by
  cbv

/-- `classifyError` maps `"fatal: cannot update HEAD"` on `symbolic-ref` to `.commandFailed`. -/
theorem symRefErr_kind :
    (Impl.classifyError "symbolic-ref"
      { exitCode := 128, stdout := ByteArray.empty, stderr := "fatal: cannot update HEAD".toUTF8 }).kind =
      .commandFailed := by
  unfold Impl.classifyError
  simp only [decodeUtf8Lossy_toUTF8_local, err5_trim_empty, Bool.false_eq_true, ↓reduceIte, err5_san]
  cbv

end LeanSwe.Git.Proofs
