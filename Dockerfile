FROM xgillard/rs_launcher

COPY . rsolve
RUN  cd /rsolve && cargo install


#CMD ["myapp"]