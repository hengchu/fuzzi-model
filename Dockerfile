FROM fpco/stack-build:lts-14.0

ENV DEBIAN_FRONTEND noninteractive

WORKDIR /tmp/z3
RUN rm /usr/bin/z3
RUN wget https://github.com/Z3Prover/z3/archive/z3-4.8.8.zip
RUN unzip z3-4.8.8.zip
RUN cd z3-z3-4.8.8 && python scripts/mk_make.py && cd build && make -j2 && make install
RUN z3 --version

RUN apt-get update -y
RUN apt-get install -y emacs vim

COPY . /tmp/fuzzi-model
WORKDIR /tmp/fuzzi-model
#RUN echo 'extra-include-dirs:\n  - /usr/local/include\nextra-lib-dirs:\n  - /usr/local/bin' >> stack.yaml
#RUN ls -alh
#RUN cat stack.yaml
RUN stack build -j2
