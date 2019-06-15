fn mean(x : &Vec<f64>) -> f64
{
    return x.iter().map(|x| *x).sum::<f64>()/(x.len() as f64);
}
fn inner_mean(x : &Vec<Vec<f64>>, n : usize) -> f64
{
    return x.iter().map(|x| x[n]).sum::<f64>()/(x.len() as f64);
}

pub (crate) fn fit(model : &mut Vec<f64>, indata : &Vec<Vec<f64>>, outdata : &Vec<f64>, rate : f64)
{
    let mut deltas = Vec::with_capacity(indata.len());
    
    for (i, input) in indata.iter().enumerate()
    {
        let mut prediction = 0.0;
        for (j, val) in input.iter().enumerate()
        {
            prediction += *val * model[j];
        }
        
        let error = outdata[i]-prediction;
        let errarray = input.iter().map(|x| x * error).collect();
        
        deltas.push(errarray);
    }
    
    for (j, data) in model.iter_mut().enumerate()
    {
        *data += inner_mean(&deltas, j)*rate;
    }
}

fn rsq(truth : &Vec<f64>, preds : &Vec<f64>) -> f64
{
    let truemean = mean(truth);
    let mut res : f64 = 0.0;
    let mut tot : f64 = 0.0;
    for i in 0..truth.len()
    {
        res += (truth[i]-preds[i]).powi(2);
        tot += (truth[i]-truemean).powi(2);
    }
    return 1.0 - res/tot;
}


pub (crate) fn predict(model : &Vec<f64>, indata : &Vec<Vec<f64>>, outdata : &Vec<f64>) -> (Vec<f64>, f64) // output, rsq
{
    let mut predictions = Vec::with_capacity(indata.len());
    
    for input in indata.iter()
    {
        let mut prediction = 0.0;
        for (j, val) in input.iter().enumerate()
        {
            prediction += *val * model[j];
        }
        
        predictions.push(prediction);
    }
    
    let rsq = rsq(outdata, &predictions);
    (predictions, rsq)
}


pub (crate) fn predict_single(model : &Vec<f64>, input : &Vec<f64>) -> f64
{
    let mut prediction = 0.0;
    for (j, val) in input.iter().enumerate()
    {
        prediction += *val * model[j];
    }
    prediction
}

//pub (crate) fn predict_single(model : &Vec<f64>, input : &Vec<f64>) -> f64
//{
//    input.iter().enumerate().map(|(j, val)| *val * model[j]).sum::<f64>()
//}
