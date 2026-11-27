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
    (coq (or (and (>= 8.16.1) (< 8.17)) (and (>= 8.18) (< 8.21))))
    (coq-mathcomp-ssreflect (and (>= 2.2.0) (< 2.3)))))

