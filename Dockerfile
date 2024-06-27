FROM coqorg/coq:8.18

RUN opam install coq-tlc
RUN opam install vscoq-language-server -y

CMD ["bash"]
