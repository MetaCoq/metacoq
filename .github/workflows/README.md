To regenerate the nix actions run the following from the top metacoq directory

```
rm .github/workflows/nix-action-*.yml
nix-shell --arg do-nothing true --run "genNixActions ; ./.nix/renameNixActions.sh"
```
