with import <nixpkgs> { };

pkgs.mkShell {
  buildInputs = with pkgs; [
    coq
  ] ++ (with pkgs.coqPackages; [
    ssreflect
    mathcomp
    mathcomp-ssreflect
    mathcomp-analysis
    QuickChick
  ]);
}
