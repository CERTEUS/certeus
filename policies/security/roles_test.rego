package roles

test_publish_afv_lex {
  allow := data.domains.lex.allow.publish
  some i
  allow[i] == "AFV"
}

test_merge_needs_atc_or_ase {
  allow := data.domains.lex.allow.merge
  # Should contain ATC and ASE
  contains(allow, "ATC")
  contains(allow, "ASE")
}

contains(arr, x) {
  some i
  arr[i] == x
}
