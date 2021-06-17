data {
    int N;
    vector[N] d_x;
    int indexer[N];
}

transformed data {
    vector[N] td_x;
    for (i in 1:N) {
        td_x[i] = exp(d_x[i]);
    }
    td_x[:] = d_x[:];
    for (i in 1:N) {
        td_x[indexer[i]] = exp(d_x[indexer[i]]);
    }
}