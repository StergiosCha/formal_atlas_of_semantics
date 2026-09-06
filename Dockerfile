FROM coqorg/coq:8.20.1

USER root
RUN apt-get update && apt-get install -y python3 python3-pip \
    && pip3 install --break-system-packages fastapi uvicorn pydantic \
    && rm -rf /var/lib/apt/lists/*

# Bake the atlas library into the image and precompile it once.
COPY --chown=coq . /atlas
WORKDIR /atlas
USER coq
# In-tree .vo files copied from the dev machine are unusable here: same Coq
# 8.20.1 but a different OCaml, and Require rejects cross-toolchain .vo
# ("inconsistent assumptions" / incompatible version). Purge and recompile
# with THIS image's coqc so Require Import mtt_ranta.MTT etc. work at runtime.
RUN find . \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' \
    -o -name '*.glob' -o -name '*.aux' \) -delete \
    && coq_makefile -f _CoqProject -o Makefile && make -j4

USER root
COPY tool/checker/server.py /srv/server.py
# The draft-and-check loop (providers.py needs AZURE_AI_KEY at runtime —
# an ACA secret, never baked into the image).
COPY tool/llm /srv/llm

# The coqorg base wraps every command in `opam exec --` (its ENTRYPOINT), and
# only the coq user has an opam root — running as root crashes at boot with
# "Opam has not been initialised". Run as coq: opam exec then also puts coqc
# on PATH, which the checker shells out to.
USER coq
EXPOSE 8477
CMD ["uvicorn", "server:app", "--app-dir", "/srv", \
     "--host", "0.0.0.0", "--port", "8477"]
