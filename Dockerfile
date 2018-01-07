FROM xgillard/rs_launcher

COPY . rsolve
RUN  cd /rsolve && cargo install


# How to use this image:
# ======================
# docker run --mount type=bind,source=/local/path,destination=/container/path \
#        xgillard/rsolve launcher -p rsolve -d /benchmarks -e cnf
#
# Example:
# ~~~~~~~~
# docker run --name agile_track \
# --mount type=bind,source=/Users/user/Documents/EXPERIMENTS/CNF_instances/Bench16/Agile,destination=/benchmarks \
# xgillard/rsolve launcher -p rsolve -d /benchmarks -t 5