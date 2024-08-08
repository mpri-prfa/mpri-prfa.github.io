all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean website

website:
	pandoc --standalone \
         --output=doc/index.html \
         --template=pandoc/template.html4 \
         --css=github-pandoc.css \
         --toc \
         --toc-depth=2 \
         --resource-path=. \
         index.md
	pandoc --standalone \
         --output=doc/installcoq.html \
         --template=pandoc/template.html4 \
         --css=github-pandoc.css \
         --resource-path=. \
         installcoq.md
