(lang dune 1.10)

(name csynth)
(source (github jfeser/csynth))
(license MIT)
(authors "Jack Feser <feser@csail.mit.edu>")
(maintainers "Jack Feser <feser@csail.mit.edu>")

(package
  (name csynth)
  (synopsis "An implementation of 'Synthesis of Loop-free Programs'")
  (depends
    (dune (and :build (>= 1.10)))

    (core (>= v0.12))
    (logs (>= 0.6))
    (ppx_compare (>= v0.12))
    (ppx_sexp_conv (>= v0.12))
    (ppx_hash (>= v0.12))
    (ppx_let (>= v0.12))

    (expect_test_helpers_kernel (and :with-test (>= v0.12)))))

(using fmt 1.1)
(generate_opam_files true)

; Local Variables:
; mode: dune
; End:
