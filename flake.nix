{
  description = "ainf";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.lean-helpers.url = "github:suiluj482/leanHelpers";
  
  outputs = { self, nixpkgs, flake-utils, lean-helpers }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          # config = {
          #   allowUnfree = true;
          #   cudaSupport = true;
          # };
        };
        pkgLeanHelpers = lean-helpers.packages.${system}.default;
      in {
        devShell = pkgs.mkShell {
          packages = with pkgs; [
            elan
            (python3.withPackages (python-pkgs: [
              python-pkgs.jax
              # python-pkgs.jax-cuda12-plugin
            ]))
          ] ++ [
            pkgLeanHelpers
          ];
          # buildInputs = with pkgs; [
          #   git gitRepo gnupg autoconf curl
          #   procps gnumake util-linux m4 gperf unzip

          #   cudatoolkit linuxPackages.nvidia_x11
            
          #   libGLU libGL
          #   xorg.libXi xorg.libXmu freeglut
          #   xorg.libXext xorg.libX11 xorg.libXv xorg.libXrandr zlib 
          #   ncurses5 stdenv.cc binutils
          # ];
          # shellHook = ''
          #     export CUDA_PATH=${pkgs.cudatoolkit}
          #     export LD_LIBRARY_PATH=${pkgs.linuxPackages.nvidia_x11}/lib:${pkgs.ncurses5}/lib
          #     export EXTRA_LDFLAGS="-L/lib -L${pkgs.linuxPackages.nvidia_x11}/lib"
          #     export EXTRA_CCFLAGS="-I/usr/include"
          # '';   
        };
      }
    );
}