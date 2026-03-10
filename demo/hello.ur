val rec
 main : (_ :: Type) -> (_ :: Type) =
  fn x : (_ :: Type) =>
   case x of
    
    {} =>
    
     return
      (Basis.join (Basis.cdata "\n")
        (Basis.join (Basis.cdata "  ")
          (Basis.join
            (Basis.tag Basis.null Basis.None Basis.noStyle Basis.None {}
              (head {})
              (Basis.join (Basis.cdata "\n")
                (Basis.join (Basis.cdata "    ")
                  (Basis.join
                    (Basis.tag Basis.null Basis.None Basis.noStyle Basis.None
                      {} (title {}) (Basis.cdata "Hello world!"))
                    (Basis.join (Basis.cdata "\n") (Basis.cdata "  "))))))
            (Basis.join (Basis.cdata "\n")
              (Basis.join (Basis.cdata "\n")
                (Basis.join (Basis.cdata "  ")
                  (Basis.join
                    (Basis.tag Basis.null Basis.None Basis.noStyle Basis.None
                      {} (body {})
                      (Basis.join (Basis.cdata "\n")
                        (Basis.join (Basis.cdata "    ")
                          (Basis.join
                            (Basis.tag Basis.null Basis.None Basis.noStyle
                              Basis.None {} (h1 {})
                              (Basis.cdata "Hello world!"))
                            (Basis.join (Basis.cdata "\n") (Basis.cdata "  "))))))
                    (Basis.cdata "\n"))))))))