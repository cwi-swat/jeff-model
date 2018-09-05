package nl.cwi.jeff_model;

import java.io.File;
import java.io.IOException;
import java.net.JarURLConnection;
import java.net.URISyntaxException;
import java.net.URL;

import org.rascalmpl.interpreter.Evaluator;
import org.rascalmpl.interpreter.control_exceptions.Throw;
import org.rascalmpl.interpreter.load.StandardLibraryContributor;
import org.rascalmpl.interpreter.load.URIContributor;

import io.usethesource.vallang.ISourceLocation;
import io.usethesource.vallang.impl.persistent.ValueFactory;




public class Transpiler{
	
	public static void main(String[] args) {
		try { 
			if (args.length != 2) {
				System.err.println(usage());
				System.exit(-1);
			}
			// Create Rascal intepreter
			Evaluator evaluator = JavaRascalContext.getEvaluator();
			//ISourceLocation moduleRoot = ValueFactory.getInstance().sourceLocation("cwd","","/Main.rsc");
			URL mainURL = Transpiler.class.getClassLoader().getResource("Main.rsc");
			final JarURLConnection connection = (JarURLConnection) mainURL.openConnection();
			final URL jarURL = connection.getJarFileURL();

			ISourceLocation moduleRoot = ValueFactory.getInstance().sourceLocation("jar+file", 
					null,jarURL.getFile()+"!/");
			
			// Add project (with Rascal modules) to search path and import module
			evaluator.addRascalSearchPathContributor(StandardLibraryContributor.getInstance());
			evaluator.addRascalSearchPathContributor(new URIContributor(moduleRoot));
			
			evaluator.doImport(null, "Main");
			
			File jeffRacketDir = new File(args[0]);
			File inputFile = new File(args[1]);
			
			// Call function (if the evaluator is shared it must be synchronized).
			synchronized (evaluator) {
				evaluator.call("transpile",  
						ValueFactory.getInstance().sourceLocation(jeffRacketDir.toURI()), 
						ValueFactory.getInstance().sourceLocation(inputFile.toURI()));
			}
		} 
		catch (Throw e) {
			// Managing Rascal exceptions
			throw new RuntimeException("Rascal call to Main::transpile failed: " + e.getMessage(), e);
		} catch (URISyntaxException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private static String usage() {
		return "Usage: Transpiler racket_dir source_file";
	}
}