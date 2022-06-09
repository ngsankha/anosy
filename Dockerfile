FROM ubuntu:21.10
RUN apt-get update && \
  DEBIAN_FRONTEND=noninteractive apt-get install -y software-properties-common git curl build-essential libssl-dev libreadline-dev zlib1g-dev libsqlite3-dev python3-pip cabal-install z3 libblas3 liblapack3 liblapack-dev libblas-dev gfortran libatlas-base-dev cmake

ENV PATH="${PATH}:/root/.local/bin"

RUN pip3 install numpy scipy matplotlib plumbum parse z3-solver

RUN curl -sSL https://get.haskellstack.org/ | sh
RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /root/liquidhaskell
RUN cd /root/liquidhaskell && git checkout 86f48a623b9a52ddbe07efc9949353518ea8185f
RUN cd /root/liquidhaskell/liquid-fixpoint && git checkout 90e19918bc51a2c246909ec1e4edba636077c675

CMD ["bash -l"]
