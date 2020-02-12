.PHONY: all browse clean

OBJDIR := build

all: $(OBJDIR)/index.html

$(OBJDIR)/index.html: $(wildcard src/**/*.thy) $(wildcard src/**/*.md)
	isabelle build -o browser_info -d . -v Index 
	cp -r "$$(isabelle getenv -b ISABELLE_BROWSER_INFO)/Unsorted/Index/." $(OBJDIR)/
	chmod -R u+w $(OBJDIR)/fonts

browse: $(OBJDIR)/index.html
	xdg-open $< 

clean:
	rm -rf $(OBJDIR)
