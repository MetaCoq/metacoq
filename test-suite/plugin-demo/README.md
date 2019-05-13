# Writing a Plugin with the Extractable Monad

You can use `Template.TemplateMonad.Extractable` to write plugins in Gallina.
You can use this project as a template for doing this.


**Beware**: Things are a little bit convoluted/brittle due to the extraction processes.
Pull requests are welcome.

## How to use it

1. Write your plugin inside the `gen-src` directory (using the `_CoqProject` in that directory). The plugin should use the `Template.TemplateMonad.Extractable` monad to interact with Coq.
2. Modify the `gen-src/Extract.v` file to extract the module that you want to call from your plugin.
3. Run `make sources` which will build the Coq sources to your plugin and extract them to OCaml.
4. In the `src` directory, write the entry point to your plugin. See `src/g_plugin_demo.ml4` for some examples. *Make sure that you do not use any names that conflict with names of `ml` files inside of `template-coq`.*
5. In the `src` directory, create an `mlpack` file which includes all the files that you need. This file *must* start with the template located in `template-coq/gen-src/meta_coq_plugin_template.mlpack` to ensure that it uses the appropriate dependencies.
6. Include any Coq files that your plugin requires in the top-level `theories` directory.
7. Build the plugin from the root directory and you should be good to go.


## How it works

As mentioned above, things are a bit brittle.
Essentially, what the `Makefile` does is first build the contents of `gen-src` to build the OCaml for the plugin.
The recursive extraction command will generate all of the files into the `src` directory, including the files that `template-coq` provides.
The top-level `Makefile` then copies the contents of the `template-coq/gen-src` directory over the `src` directory before building it to ensure that everything is consistent.
