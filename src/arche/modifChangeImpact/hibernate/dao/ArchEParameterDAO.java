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

package arche.modifChangeImpact.hibernate.dao;

/**
 * Utility class that implements the Hibernate-SQL queries to restore, save, update 
 * and delete parameters for responsibilities or relations in ArchE. Parameters can 
 * be of types boolean, integer, double or string
 * 
 * @author Andres Diaz-Pace
 */

import java.util.Iterator;
import java.util.List;

import org.hibernate.Hibernate;
import org.hibernate.Query;
import org.hibernate.Session;
import org.hibernate.type.Type;

import edu.cmu.sei.arche.external.data.ArchEVersion;

import arche.modifChangeImpact.hibernate.vo.ArchERelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;

public class ArchEParameterDAO {
	
	public static Double findDoubleParameter(String table, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {
		
		Object value = findParameterValueByOwner(owner.getFactId(),version.getId(), 
				table, openSession,Hibernate.DOUBLE);
		return ((Double)value);
	}

	public static Double findDoubleParameter(String table, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {
		
		Object value = findParameterValueByOwner(owner.getFactId(),version.getId(), 
				table, openSession,Hibernate.DOUBLE);
		return ((Double)value);
	}

	public static String findStringParameter(String table, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {
		
		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
				table, openSession,Hibernate.TEXT);
		return ((String)value);
	}

	public static String findStringParameter(String table, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {

		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
				table, openSession,Hibernate.TEXT);
		return ((String)value);
	}

	public static Boolean findBooleanParameter(String table, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {

//		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
//				table, openSession,Hibernate.BOOLEAN);
//		return ((Boolean)value);
		// This is so because BOOLEAN is not a predefined type in MySQL
		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
				table, openSession,Hibernate.STRING);
		return (Boolean.getBoolean((String)value));
	}

	public static Boolean findBooleanParameter(String table, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {

//		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
//					table, openSession,Hibernate.BOOLEAN);
//		return ((Boolean)value);
		// This is so because BOOLEAN is not a predefined type in MySQL
		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
				table, openSession,Hibernate.STRING);		
		return (Boolean.getBoolean((String)value));
	}

	public static Integer findIntegerParameter(String table, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {

		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
				table, openSession,Hibernate.INTEGER);
		return ((Integer)value);
	}

	public static Integer findIntegerParameter(String table, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {

		Object value = findParameterValueByOwner(owner.getFactId(), version.getId(), 
				table, openSession,Hibernate.INTEGER);
		return ((Integer)value);
	}

	private static Object findParameterValueByOwner(String factid, int version, String parameterTable, 
			Session session, Type hibernateType) {

		// This kind of queries can be alternatively defined in a mapping file 
		// as "named sql queries"
		String SQL_STATEMENT ="SELECT value FROM "+parameterTable+" WHERE owner = ? AND version = ?";
		Query sqlQuery = session.createSQLQuery(SQL_STATEMENT)
			.addScalar("value",hibernateType)
			.setString(0, factid)
			.setInteger(1, version);

		Object propertyValue = sqlQuery.uniqueResult();
		return (propertyValue);
	}
	
	public static void saveOrUpdateDoubleParameter(String table, Double value,
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {		

		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.DOUBLE);
		return;
	}

	public static void saveOrUpdateDoubleParameter(String table, Double value, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {		
		
		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.DOUBLE);
		return;
	}

	public static void saveOrUpdateStringParameter(String table, String value, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {		
		
		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.STRING);
		return;
	}
	
	public static void saveOrUpdateStringParameter(String table, String value, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {		

		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.STRING);
		return;
	}

	
	public static void saveOrUpdateBooleanParameter(String table, Boolean value, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {		

//		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.BOOLEAN);
		// This is so because BOOLEAN is not a predefined type in MySQL
		String stringValue = value.toString();
		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, stringValue, openSession,Hibernate.STRING);
		return;
	}

	public static void saveOrUpdateBooleanParameter(String table, Boolean value, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {		
		
//		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.BOOLEAN);
		// This is so because BOOLEAN is not a predefined type in MySQL
		String stringValue = value.toString();
		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, stringValue, openSession,Hibernate.STRING);
		return;
	}

	public static void saveOrUpdateIntegerParameter(String table, Integer value, 
		ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {		
		
		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.INTEGER);
		return;
	}

	public static void saveOrUpdateIntegerParameter(String table, Integer value, 
		ArchERelationVO owner, ArchEVersion version, Session openSession) {		

		saveOrUpdateParameterByOwner(owner.getFactId(), version, table, value, openSession,Hibernate.INTEGER);
		return;
	}

	private static int saveOrUpdateParameterByOwner(String factid, ArchEVersion version, 
			String parameterTable, Object value, Session session, Type hibernateType) {
		
		Integer uid = findParameterUidByOwner(factid, version.getId(),parameterTable,session);
		
		Query sqlQuery = null;
		
		if (uid == null) { // The parameter requires a new record in the table
		
			String SQL_INSERT ="INSERT INTO "+parameterTable+" (version, `fact-id`, value, owner, source, status)" 
					+ "VALUES (:version, :factid, :newValue, :owner, :source, :status)";
			sqlQuery = session.createSQLQuery(SQL_INSERT)
				.setInteger("version", version.getId())
				.setString("factid", version.generateUniqueFactID())
				.setString("owner", factid)
				.setString("source", "ArchE")
				.setString("status", "none");			
		}
		else { // It's simply an update of the value for an existing record

			String SQL_UPDATE ="UPDATE "+parameterTable+" SET value = :newValue WHERE uid = :foundUid";
			sqlQuery = session.createSQLQuery(SQL_UPDATE)
				.setInteger("foundUid", uid);
		}
		
		if (hibernateType.equals(Hibernate.DOUBLE))
			sqlQuery.setDouble("newValue", (Double)value);
		else if (hibernateType.equals(Hibernate.STRING))
			sqlQuery.setString("newValue", (String)value);			
		else if (hibernateType.equals(Hibernate.INTEGER))
			sqlQuery.setInteger("newValue", (Integer)value);			
		else if (hibernateType.equals(Hibernate.BOOLEAN))
			sqlQuery.setBoolean("newValue", (Boolean)value);

		int result = sqlQuery.executeUpdate();
		//System.out.println("UID for record in "+parameterTable+" "+uid+" value="+value+" result= "+result);

		return (result);		
	}

	private static Integer findParameterUidByOwner(String factid, int version, 
			String parameterTable,	Session session) {

		// This kind of queries can be alternatively defined in a mapping file as "named sql queries"
		String SQL_STATEMENT ="Select uid from "+parameterTable+" where owner = ? and version = ?";
		Query sqlQuery = session.createSQLQuery(SQL_STATEMENT)
			.addScalar("uid",Hibernate.INTEGER)
			.setString(0, factid)
			.setInteger(1, version);

		Integer uid = (Integer)(sqlQuery.uniqueResult());
		return (uid);
	}
	
	public static void deleteParameter(String parameterName, String table, 
			ArchEResponsibilityVO owner, ArchEVersion version, Session openSession) {		
			
		Integer uid = findParameterUidByOwner(owner.getFactId(), version.getId(),table, openSession);
		
		if (uid != null)
			deleteParameterByUid(uid, table, openSession);
		
		return;
	}

	public static void deleteParameter(String parameterName, String table, 
			ArchERelationVO owner, ArchEVersion version, Session openSession) {		
			
		Integer uid = findParameterUidByOwner(owner.getFactId(), version.getId(),table, openSession);
		
		if (uid != null)
			deleteParameterByUid(uid, table, openSession);
		
		return;
	}

	private static void deleteParameterByUid(Integer uid, String parameterTable, Session session) {
			
		String SQL_DELETE ="DELETE FROM "+parameterTable+" WHERE uid = ?";
		Query sqlQuery = session.createSQLQuery(SQL_DELETE)
			.setInteger(0,uid);

		sqlQuery.executeUpdate();
		
		return;
	}
	
	public static void deleteParametersBySetOfResponsibilities(List setOwners, ArchEVersion version, 
			String parameterTable, Session session) {
		
		String[] validFactIds = new String[setOwners.size()];
		int index = 0;
		for (Iterator it = setOwners.iterator(); it.hasNext(); ) {
			validFactIds[index] = ((ArchEResponsibilityVO)(it.next())).getFactId();
			index++;
		}

		Query sqlQuery = null;
		if (validFactIds.length > 0) {
			//List list = Arrays.asList(validFactIds);
			String SQL_DELETE ="DELETE FROM "+parameterTable+" WHERE version = :versionNumber AND owner NOT IN ( :validFactIds )";
			sqlQuery = session.createSQLQuery(SQL_DELETE)
				.setInteger("versionNumber", version.getId())
				.setParameterList("validFactIds", validFactIds);		
		}
		else {
			String SQL_DELETE ="DELETE FROM "+parameterTable+" WHERE version = :versionNumber";
			sqlQuery = session.createSQLQuery(SQL_DELETE)
				.setInteger("versionNumber", version.getId());
		}
	
		int n = sqlQuery.executeUpdate();		

		return;
	}

	public static void deleteParametersBySetOfRelations(List setOwners, ArchEVersion version, 
			String parameterTable, Session session) {	
	
		String[] validFactIds = new String[setOwners.size()];
		int index = 0;
		for (Iterator it = setOwners.iterator(); it.hasNext(); ) {
			validFactIds[index] = ((ArchERelationVO)(it.next())).getFactId();
			index++;
		}

		Query sqlQuery = null;
		if (validFactIds.length > 0) {
			String SQL_DELETE ="DELETE FROM "+parameterTable+" WHERE version = :versionNumber AND owner NOT IN ( :validFactIds )";
			sqlQuery = session.createSQLQuery(SQL_DELETE)
				.setInteger("versionNumber", version.getId())
				.setParameterList("validFactIds", validFactIds);
		}
		else {
			String SQL_DELETE ="DELETE FROM "+parameterTable+" WHERE version = :versionNumber";
			sqlQuery = session.createSQLQuery(SQL_DELETE)
				.setInteger("versionNumber", version.getId());
		}
	
		int n = sqlQuery.executeUpdate();		
		
		return;
	}

} 
