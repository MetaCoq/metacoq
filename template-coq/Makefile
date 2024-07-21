all: coq template-coq plugin

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

_TemplateCoqProject: _TemplateCoqProject.in metacoq-config
	cat metacoq-config > _TemplateCoqProject
	cat _TemplateCoqProject.in >> _TemplateCoqProject


Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.template: _TemplateCoqProject
	coq_makefile -f _TemplateCoqProject -o Makefile.template
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.template/g Makefile.template > Makefile.template.tmp && mv -f Makefile.template.tmp Makefile.template

.merlin: Makefile.plugin
	[ -e "gen-src/signature.mli" ] && $(MAKE) -f $< $@

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

# The template-coq plugin to run template programs live in Coq
template-coq: coq Makefile.template
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.template optfiles
	$(MAKE) -f Makefile.template

# The extractable template plugin to run *extracted* template programs in OCaml
# The sources of the plugin are built by the coq target, which calls the
# ./update_plugin.sh after successfull extraction.

plugin: coq template-coq Makefile.plugin
	$(MAKE) -f Makefile.plugin

.PHONY: install html clean mrproper all plugin

install: Makefile.coq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.template install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.coq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.coq uninstall
	$(MAKE) -f Makefile.template uninstall
	$(MAKE) -f Makefile.plugin uninstall

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.template clean
	$(MAKE) -f Makefile.plugin clean

mrproper:
	rm -f Makefile.coq
	rm -f Makefile.plugin
	rm -f Makefile.template

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

PLUGIN_PROJECT_BLACKLIST := \
	mCUint63 \
	#

space := $(subst ,, )

PLUGIN_PROJECT_BLACKLIST_SED:=\($(subst $(space),\|,$(PLUGIN_PROJECT_BLACKLIST))\)\.\(ml\|mli\)

.PHONY: update-_PluginProject.in
update-_PluginProject.in:
	@echo 'WARNING: This target only works correctly when gen-src has been populated from making Extraction.vo and contains no outdated .ml{,i} files'
	contents="$$(cat _PluginProject.in | grep -v '^\(# \|\)gen-src/.*\.\(mli\|ml\)$$')"; \
	line="$$(printf "%s\n" "$${contents}" | grep -n "^# Generated" | head -1 | cut -d: -f1)"; \
	{ printf "%s\n" "$${contents}" | head -n$${line}; \
	  ls -1 gen-src/*.ml gen-src/*.mli | env LC_COLLATE=C sort | sed 's,^\(gen-src/$(PLUGIN_PROJECT_BLACKLIST_SED)\)$$,# \1,g'; \
	  printf "%s\n" "$${contents}" | tail -n+$$((line+1)); \
	} > _PluginProject.in
