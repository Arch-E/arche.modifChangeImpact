/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact.hibernate;

/**
 * An Hibernate-based implementation of ArchEDataProvider for ArchE database
 * <p>
 * The most common pattern in a client/server application is "session-per-request with detached objects".
 * We use a single database transaction to serve a client request, starting and
 * committing it when we open and close the Session. The relationship between the two
 * is one-to-one. Hibernate even help simplify this pattern by providing its built-in
 * "current session" context management. All we have to do is start a transaction
 * when a client request has to be processed, and end the transaction before the response
 * is sent to the client. 
 * <p>
 * In short, when you start a transaction, a JDBC connection is established and a session is open.
 * When you end the transaction, the JDBC connection is disconnected and the session is closed. 
 * In this way, you don't need to directly handle JDBC connection/disconnection as well as session
 * lifetime.
 * 
 * @author Hyunwoo Kim, Andres Diaz-Pace
 */

import org.hibernate.HibernateException;
import org.hibernate.SessionFactory;
import org.hibernate.cfg.Configuration;

import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEArchitecture;
import edu.cmu.sei.arche.external.data.ArchEDataProvider;
import edu.cmu.sei.arche.external.data.ArchERequirementModel;
import edu.cmu.sei.arche.external.data.ArchEVersion;

public abstract class ArchECoreDataProvider implements ArchEDataProvider {

    protected static final SessionFactory sessionFactory;

    static { // Initialization code for the Hibernate session factory
    	try {
			Class.forName("com.mysql.jdbc.Driver");
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
		
        try {
            // Create the SessionFactory from hibernate.cfg.xml
            sessionFactory = new Configuration().configure().buildSessionFactory();
        } catch (Throwable ex) {
            // Make sure you log the exception, as it might be swallowed
            System.err.println("Initial SessionFactory creation failed." + ex);
            throw new ExceptionInInitializerError(ex);
        }       
        
    }
    
    public static SessionFactory getSessionFactory() {
        return sessionFactory;
    }

    /**
     * Restore a requirement model from DB
     * 
	 * @param version The version for the requirement model being restored 
	 * @throws ArchEException      
     */    
	public ArchERequirementModel restoreRequirementModel(ArchEVersion version) throws ArchEException {
		ArchECoreRequirementModel requirementModel = null;
		
	    try {	    	
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					
	    	
			// currentVersion and restore a requirement model for the given reasoning framework
			requirementModel = this.newRequirementModel((ArchEVersionVO)version);								
			requirementModel.restore();										
			
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			return requirementModel;
			
	    } catch (HibernateException ex) {
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());
	    }		
		
	}
	
    /**
     * Save a requirement model in DB
     *       
	 * @param requirementModel The requirement model instance being saved
	 * @throws ArchEException      
     */    
	public void saveRequirementModel(ArchERequirementModel requirementModel) throws ArchEException{
	    try {	    	
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					

	    	// Save this architecture in DB
	    	((ArchECoreRequirementModel)requirementModel).save();					
	    	
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			
	    } catch (HibernateException ex) {
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());
	    }					
	}
	
    /**
     * Save as a requirement model in DB     * 
     *       
	 * @param requirementModel The requirement model instance being saved
	 * @param newVersion The version for that requirement model
	 * @throws ArchEException      
     */    
	public void saveRequirementModelAs(ArchERequirementModel requirementModel, 
				ArchEVersion newVersion) throws ArchEException {
	    try {	    	
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					

	    	// Save this architecture in DB
	    	((ArchECoreRequirementModel)requirementModel).saveAs((ArchEVersionVO)newVersion);					
	    	
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			
	    } catch (HibernateException ex) {
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());
	    }					
	}
	
    /**
     * Restore an architecture from DB     
     * 
	 * @param version The version for the architecture being restored 
	 * @throws ArchEException      
     */    
	public ArchEArchitecture restoreArchitecture(ArchEVersion version) throws ArchEException {
		ArchECoreArchitecture architecture = null;
		
	    try {	    	
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					
	    	
			// Create an architecture instance
			architecture = this.newArchitecture((ArchEVersionVO)version);
			
			// Create an instance of a responsibility structure and attach each other
			ArchECoreResponsibilityStructure coreRS = 
					(ArchECoreResponsibilityStructure)this.newResponsibilityStructure(architecture);
			architecture.setResponsibilityStructure(coreRS);						
			
			// Create an instance of a custom view by calling 'creatView()' method of the given reasoning framework.
			// RF developers need to implement the createView() method to provide their custom view.
			// If not implemented, it must return null.
			// Associate each other
			ArchECoreView coreView = 
					(ArchECoreView)this.newView(architecture);
			architecture.setView(coreView);
				
			// Restore an architecture from DB
			architecture.restore();				
			
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			return architecture;
			
	    } catch (HibernateException ex) {
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());
	    } 
	}
	
	
	/**
	 * Save the given architecture in DB.  
     * 
	 * @param architecture The architecture instance being saved
	 * @throws ArchEException      
	 */
	public void saveArchitecture(ArchEArchitecture architecture) throws ArchEException{		
				
	    try {	    	
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					

	    	// Save this architecture in DB
	    	((ArchECoreArchitecture)architecture).save();					
	    	
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			
	    } catch (HibernateException ex) {
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());
	    }				
	}
	
	/**
	 * Save the given architecture with a new version in DB.  
	 * 
	 * If the architecture with the given version already exists in DB,
	 * delete it from DB and then save the given local architecture with the version in DB. 
	 * Otherwise, save the local architecture in DB with the given version.
     * 
	 * @param architecture The architecture instance being saved as a new alternative
	 * @param newVersion The version for that architecture 
	 * @throws ArchEException      
	 */
	public void saveArchitectureAs(ArchEArchitecture architecture,ArchEVersion newVersion) throws ArchEException{		
				
	    try {	    	
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					

			// Persist the architecture with a new version
			((ArchECoreArchitecture)architecture).saveAs((ArchEVersionVO)newVersion);				
			
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			
	    } catch (HibernateException ex) {
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());
	    }				
	}

	
	public void deleteArchitecture(ArchEVersion version) throws ArchEException{
		try{			
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					
	    	
			// TODO: Need to check if this line works or not
			ArchEVersionVO versionVO = (ArchEVersionVO)version;
			sessionFactory.getCurrentSession().delete(versionVO);		
			
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
		} catch (HibernateException ex){
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());			
		}		
	}

	public ArchEVersion getVersion(String architectureName) throws ArchEException {		
		try{			
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					
	    	
	    	// Get the version information with the given architecture name from DB
			ArchEVersionVO version = (ArchEVersionVO)(sessionFactory.getCurrentSession().createQuery("from ArchEVersionVO as v where v.versionName = ?")
				.setString(0, architectureName).uniqueResult());
			
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();			
			
	    	return (ArchEVersion)(version);		
		} catch (HibernateException ex){
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());			
		}		
	}	

//	public ArchEVersion getParentVersion(String architectureName) throws ArchEException {		
//		try{			
//			// Begin unit of work (transaction == session) in Hibernate, which means
//	    	// 	1) Open a session
//	    	// 	2) Open a JDBC connection
//	    	// 	3) Start a transaction
//	    	sessionFactory.getCurrentSession().beginTransaction();					
//	    	
//	    	// Get the version information with the given architecture name from DB
//			ArchEVersionVO version = (ArchEVersionVO)(sessionFactory.getCurrentSession().createQuery("from ArchEVersionVO as v where v.versionName = ?")
//				.setString(0, architectureName).uniqueResult());
//
//			ArchEVersionVO parentVersion = (ArchEVersionVO)(sessionFactory.getCurrentSession().createQuery("from ArchEVersionVO as v where v.id = ?")
//					.setInteger(0, version.getId()).uniqueResult());
//	
//			// End unit of work (transaction == session) in Hibernate, which means
//	    	// 	1) End the transaction by commit
//	    	// 	2) Close the JDBC connection
//	    	// 	3) Close the session
//			sessionFactory.getCurrentSession().getTransaction().commit();			
//			
//	    	return (ArchEVersion)(parentVersion);		
//		} catch (HibernateException ex){
//	    	// If any problem occurred, an exception will be thrown and
//			// end unit of work in Hibernate, which means
//	    	// 	1) End the transaction by rollback
//	    	// 	2) Close the JDBC connection
//	    	// 	3) Close the session
//	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
//	        throw new ArchEException(ex.getMessage(),ex.getCause());			
//		}		
//	}	

	public ArchEVersion newChildVersion(ArchEVersion parentVersion, String architectureName) throws ArchEException {
		try{			
			// Begin unit of work (transaction == session) in Hibernate, which means
	    	// 	1) Open a session
	    	// 	2) Open a JDBC connection
	    	// 	3) Start a transaction
	    	sessionFactory.getCurrentSession().beginTransaction();					
	    		    	
	    	// Create a new version instance
			String storageType = "temp";
	    	String factSetName = "Design";	    	
	    	ArchEVersionVO version = new ArchEVersionVO(architectureName, storageType, factSetName);
	    	
	    	version.setParent(parentVersion.getId());
	    	version.setMaxFactID(parentVersion.getMaxFactID()+1000);
	    	
	    	// Save it in the Hibernate seesion memory
	    	sessionFactory.getCurrentSession().save(version);
	    	
			// End unit of work (transaction == session) in Hibernate, which means
	    	// 	1) End the transaction by commit
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
			sessionFactory.getCurrentSession().getTransaction().commit();				    	
			
	    	return (ArchEVersion )version;
		} catch (HibernateException ex){
	    	// If any problem occurred, an exception will be thrown and
			// end unit of work in Hibernate, which means
	    	// 	1) End the transaction by rollback
	    	// 	2) Close the JDBC connection
	    	// 	3) Close the session
	    	sessionFactory.getCurrentSession().getTransaction().rollback();		
	        throw new ArchEException(ex.getMessage(),ex.getCause());			
		}		
    }
	
	/////////////////////////////////////////////////////////////////////////////////////
	// Abstract methods 

    /** 
     * Must implement this method. You need to simply create an instance of your requirement model class
     * and return it. 
     * 
     * @param version the input version information which a newly-created requirement model will belong to
     * @return the ArchECoreRequirementModel instance created. 
     * @exception ArchEException
     */    
    public abstract ArchECoreRequirementModel newRequirementModel(ArchEVersionVO version) throws ArchEException;
	
    /** 
     * Must implement this method. You need to simply create an instance of your architecture class
     * and return it. 
     * 
     * @param version the input version information which a newly-created architecture will belong to
     * @return the ArchECoreArchitecture instance created. 
     * @exception ArchEException
     */    
    public abstract ArchECoreArchitecture newArchitecture(ArchEVersionVO version) throws ArchEException;

    /** 
     * Must implement this method. You need to simply create an instance of your responsibility structure class
     * and return it. 
     * 
     * @param architecture the input parent architecture of a newly-created responsibility structure
     * @return the ArchECoreResponsibilityStructure instance created. 
     * @exception ArchEException
     */    
    public abstract ArchECoreResponsibilityStructure newResponsibilityStructure(ArchECoreArchitecture architecture) throws ArchEException;
    
    /** 
     * Implement this method iff your reasoning framework has its own view to analyze or to which
     * a tactic is applied. You need to simply create an instance of your view class and return it. 
     * 
     * @param architecture the input parent architecture of a newly-created view
     * @return the ArchECoreView instance created. If your reasoning framework will support only
     * analysis, just return null.
     * @exception ArchEException
     */    
    public abstract ArchECoreView newView(ArchECoreArchitecture architecture) throws ArchEException;
	
}

