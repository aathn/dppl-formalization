FROM coqorg/coq

RUN opam install coq-tlc
RUN opam install vscoq-language-server -y

CMD ["bash"]