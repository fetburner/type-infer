(lang dune 2.5)
(using coq 0.2)

(name coq-type-infer)

(generate_opam_files true)

(license MIT)
(authors "Masayuki Mizuno <mizuno@wantedly.com>")
(maintainers "Masayuki Mizuno <mizuno@wantedly.com>")
(source (github fetburner/type-infer))

(package
  (name coq-type-infer)
  (synopsis "A formal verification of algorithm W")
  (depends
    (rocq-core (and (>= 9.0) (< 9.4)))
    (rocq-stdlib (>= 9.0))
    (coq-core (>= 9.0))
    (rocq-mathcomp-boot (and (>= 2.6.0) (< 2.7)))))

